/*! cornerstoneWidget - v0.0.0 - 2015-04-14 | (c) 2015 Erik Ziegler | https://github.com/swederik/cornerstoneWidget */
//Not using strict: uneven strict support in browsers, #392, and causes
//problems with requirejs.exec()/transpiler plugins that may not be strict.
/*jslint regexp: true, nomen: true, sloppy: true */
/*global window, navigator, document, importScripts, setTimeout, opera */

var requirejs, require, define;
(function (global) {
    var req, s, head, baseElement, dataMain, src,
        interactiveScript, currentlyAddingScript, mainScript, subPath,
        version = '2.1.17',
        commentRegExp = /(\/\*([\s\S]*?)\*\/|([^:]|^)\/\/(.*)$)/mg,
        cjsRequireRegExp = /[^.]\s*require\s*\(\s*["']([^'"\s]+)["']\s*\)/g,
        jsSuffixRegExp = /\.js$/,
        currDirRegExp = /^\.\//,
        op = Object.prototype,
        ostring = op.toString,
        hasOwn = op.hasOwnProperty,
        ap = Array.prototype,
        apsp = ap.splice,
        isBrowser = !!(typeof window !== 'undefined' && typeof navigator !== 'undefined' && window.document),
        isWebWorker = !isBrowser && typeof importScripts !== 'undefined',
        //PS3 indicates loaded and complete, but need to wait for complete
        //specifically. Sequence is 'loading', 'loaded', execution,
        // then 'complete'. The UA check is unfortunate, but not sure how
        //to feature test w/o causing perf issues.
        readyRegExp = isBrowser && navigator.platform === 'PLAYSTATION 3' ?
                      /^complete$/ : /^(complete|loaded)$/,
        defContextName = '_',
        //Oh the tragedy, detecting opera. See the usage of isOpera for reason.
        isOpera = typeof opera !== 'undefined' && opera.toString() === '[object Opera]',
        contexts = {},
        cfg = {},
        globalDefQueue = [],
        useInteractive = false;

    function isFunction(it) {
        return ostring.call(it) === '[object Function]';
    }

    function isArray(it) {
        return ostring.call(it) === '[object Array]';
    }

    /**
     * Helper function for iterating over an array. If the func returns
     * a true value, it will break out of the loop.
     */
    function each(ary, func) {
        if (ary) {
            var i;
            for (i = 0; i < ary.length; i += 1) {
                if (ary[i] && func(ary[i], i, ary)) {
                    break;
                }
            }
        }
    }

    /**
     * Helper function for iterating over an array backwards. If the func
     * returns a true value, it will break out of the loop.
     */
    function eachReverse(ary, func) {
        if (ary) {
            var i;
            for (i = ary.length - 1; i > -1; i -= 1) {
                if (ary[i] && func(ary[i], i, ary)) {
                    break;
                }
            }
        }
    }

    function hasProp(obj, prop) {
        return hasOwn.call(obj, prop);
    }

    function getOwn(obj, prop) {
        return hasProp(obj, prop) && obj[prop];
    }

    /**
     * Cycles over properties in an object and calls a function for each
     * property value. If the function returns a truthy value, then the
     * iteration is stopped.
     */
    function eachProp(obj, func) {
        var prop;
        for (prop in obj) {
            if (hasProp(obj, prop)) {
                if (func(obj[prop], prop)) {
                    break;
                }
            }
        }
    }

    /**
     * Simple function to mix in properties from source into target,
     * but only if target does not already have a property of the same name.
     */
    function mixin(target, source, force, deepStringMixin) {
        if (source) {
            eachProp(source, function (value, prop) {
                if (force || !hasProp(target, prop)) {
                    if (deepStringMixin && typeof value === 'object' && value &&
                        !isArray(value) && !isFunction(value) &&
                        !(value instanceof RegExp)) {

                        if (!target[prop]) {
                            target[prop] = {};
                        }
                        mixin(target[prop], value, force, deepStringMixin);
                    } else {
                        target[prop] = value;
                    }
                }
            });
        }
        return target;
    }

    //Similar to Function.prototype.bind, but the 'this' object is specified
    //first, since it is easier to read/figure out what 'this' will be.
    function bind(obj, fn) {
        return function () {
            return fn.apply(obj, arguments);
        };
    }

    function scripts() {
        return document.getElementsByTagName('script');
    }

    function defaultOnError(err) {
        throw err;
    }

    //Allow getting a global that is expressed in
    //dot notation, like 'a.b.c'.
    function getGlobal(value) {
        if (!value) {
            return value;
        }
        var g = global;
        each(value.split('.'), function (part) {
            g = g[part];
        });
        return g;
    }

    /**
     * Constructs an error with a pointer to an URL with more information.
     * @param {String} id the error ID that maps to an ID on a web page.
     * @param {String} message human readable error.
     * @param {Error} [err] the original error, if there is one.
     *
     * @returns {Error}
     */
    function makeError(id, msg, err, requireModules) {
        var e = new Error(msg + '\nhttp://requirejs.org/docs/errors.html#' + id);
        e.requireType = id;
        e.requireModules = requireModules;
        if (err) {
            e.originalError = err;
        }
        return e;
    }

    if (typeof define !== 'undefined') {
        //If a define is already in play via another AMD loader,
        //do not overwrite.
        return;
    }

    if (typeof requirejs !== 'undefined') {
        if (isFunction(requirejs)) {
            //Do not overwrite an existing requirejs instance.
            return;
        }
        cfg = requirejs;
        requirejs = undefined;
    }

    //Allow for a require config object
    if (typeof require !== 'undefined' && !isFunction(require)) {
        //assume it is a config object.
        cfg = require;
        require = undefined;
    }

    function newContext(contextName) {
        var inCheckLoaded, Module, context, handlers,
            checkLoadedTimeoutId,
            config = {
                //Defaults. Do not set a default for map
                //config to speed up normalize(), which
                //will run faster if there is no default.
                waitSeconds: 7,
                baseUrl: './',
                paths: {},
                bundles: {},
                pkgs: {},
                shim: {},
                config: {}
            },
            registry = {},
            //registry of just enabled modules, to speed
            //cycle breaking code when lots of modules
            //are registered, but not activated.
            enabledRegistry = {},
            undefEvents = {},
            defQueue = [],
            defined = {},
            urlFetched = {},
            bundlesMap = {},
            requireCounter = 1,
            unnormalizedCounter = 1;

        /**
         * Trims the . and .. from an array of path segments.
         * It will keep a leading path segment if a .. will become
         * the first path segment, to help with module name lookups,
         * which act like paths, but can be remapped. But the end result,
         * all paths that use this function should look normalized.
         * NOTE: this method MODIFIES the input array.
         * @param {Array} ary the array of path segments.
         */
        function trimDots(ary) {
            var i, part;
            for (i = 0; i < ary.length; i++) {
                part = ary[i];
                if (part === '.') {
                    ary.splice(i, 1);
                    i -= 1;
                } else if (part === '..') {
                    // If at the start, or previous value is still ..,
                    // keep them so that when converted to a path it may
                    // still work when converted to a path, even though
                    // as an ID it is less than ideal. In larger point
                    // releases, may be better to just kick out an error.
                    if (i === 0 || (i === 1 && ary[2] === '..') || ary[i - 1] === '..') {
                        continue;
                    } else if (i > 0) {
                        ary.splice(i - 1, 2);
                        i -= 2;
                    }
                }
            }
        }

        /**
         * Given a relative module name, like ./something, normalize it to
         * a real name that can be mapped to a path.
         * @param {String} name the relative name
         * @param {String} baseName a real name that the name arg is relative
         * to.
         * @param {Boolean} applyMap apply the map config to the value. Should
         * only be done if this normalization is for a dependency ID.
         * @returns {String} normalized name
         */
        function normalize(name, baseName, applyMap) {
            var pkgMain, mapValue, nameParts, i, j, nameSegment, lastIndex,
                foundMap, foundI, foundStarMap, starI, normalizedBaseParts,
                baseParts = (baseName && baseName.split('/')),
                map = config.map,
                starMap = map && map['*'];

            //Adjust any relative paths.
            if (name) {
                name = name.split('/');
                lastIndex = name.length - 1;

                // If wanting node ID compatibility, strip .js from end
                // of IDs. Have to do this here, and not in nameToUrl
                // because node allows either .js or non .js to map
                // to same file.
                if (config.nodeIdCompat && jsSuffixRegExp.test(name[lastIndex])) {
                    name[lastIndex] = name[lastIndex].replace(jsSuffixRegExp, '');
                }

                // Starts with a '.' so need the baseName
                if (name[0].charAt(0) === '.' && baseParts) {
                    //Convert baseName to array, and lop off the last part,
                    //so that . matches that 'directory' and not name of the baseName's
                    //module. For instance, baseName of 'one/two/three', maps to
                    //'one/two/three.js', but we want the directory, 'one/two' for
                    //this normalization.
                    normalizedBaseParts = baseParts.slice(0, baseParts.length - 1);
                    name = normalizedBaseParts.concat(name);
                }

                trimDots(name);
                name = name.join('/');
            }

            //Apply map config if available.
            if (applyMap && map && (baseParts || starMap)) {
                nameParts = name.split('/');

                outerLoop: for (i = nameParts.length; i > 0; i -= 1) {
                    nameSegment = nameParts.slice(0, i).join('/');

                    if (baseParts) {
                        //Find the longest baseName segment match in the config.
                        //So, do joins on the biggest to smallest lengths of baseParts.
                        for (j = baseParts.length; j > 0; j -= 1) {
                            mapValue = getOwn(map, baseParts.slice(0, j).join('/'));

                            //baseName segment has config, find if it has one for
                            //this name.
                            if (mapValue) {
                                mapValue = getOwn(mapValue, nameSegment);
                                if (mapValue) {
                                    //Match, update name to the new value.
                                    foundMap = mapValue;
                                    foundI = i;
                                    break outerLoop;
                                }
                            }
                        }
                    }

                    //Check for a star map match, but just hold on to it,
                    //if there is a shorter segment match later in a matching
                    //config, then favor over this star map.
                    if (!foundStarMap && starMap && getOwn(starMap, nameSegment)) {
                        foundStarMap = getOwn(starMap, nameSegment);
                        starI = i;
                    }
                }

                if (!foundMap && foundStarMap) {
                    foundMap = foundStarMap;
                    foundI = starI;
                }

                if (foundMap) {
                    nameParts.splice(0, foundI, foundMap);
                    name = nameParts.join('/');
                }
            }

            // If the name points to a package's name, use
            // the package main instead.
            pkgMain = getOwn(config.pkgs, name);

            return pkgMain ? pkgMain : name;
        }

        function removeScript(name) {
            if (isBrowser) {
                each(scripts(), function (scriptNode) {
                    if (scriptNode.getAttribute('data-requiremodule') === name &&
                            scriptNode.getAttribute('data-requirecontext') === context.contextName) {
                        scriptNode.parentNode.removeChild(scriptNode);
                        return true;
                    }
                });
            }
        }

        function hasPathFallback(id) {
            var pathConfig = getOwn(config.paths, id);
            if (pathConfig && isArray(pathConfig) && pathConfig.length > 1) {
                //Pop off the first array value, since it failed, and
                //retry
                pathConfig.shift();
                context.require.undef(id);

                //Custom require that does not do map translation, since
                //ID is "absolute", already mapped/resolved.
                context.makeRequire(null, {
                    skipMap: true
                })([id]);

                return true;
            }
        }

        //Turns a plugin!resource to [plugin, resource]
        //with the plugin being undefined if the name
        //did not have a plugin prefix.
        function splitPrefix(name) {
            var prefix,
                index = name ? name.indexOf('!') : -1;
            if (index > -1) {
                prefix = name.substring(0, index);
                name = name.substring(index + 1, name.length);
            }
            return [prefix, name];
        }

        /**
         * Creates a module mapping that includes plugin prefix, module
         * name, and path. If parentModuleMap is provided it will
         * also normalize the name via require.normalize()
         *
         * @param {String} name the module name
         * @param {String} [parentModuleMap] parent module map
         * for the module name, used to resolve relative names.
         * @param {Boolean} isNormalized: is the ID already normalized.
         * This is true if this call is done for a define() module ID.
         * @param {Boolean} applyMap: apply the map config to the ID.
         * Should only be true if this map is for a dependency.
         *
         * @returns {Object}
         */
        function makeModuleMap(name, parentModuleMap, isNormalized, applyMap) {
            var url, pluginModule, suffix, nameParts,
                prefix = null,
                parentName = parentModuleMap ? parentModuleMap.name : null,
                originalName = name,
                isDefine = true,
                normalizedName = '';

            //If no name, then it means it is a require call, generate an
            //internal name.
            if (!name) {
                isDefine = false;
                name = '_@r' + (requireCounter += 1);
            }

            nameParts = splitPrefix(name);
            prefix = nameParts[0];
            name = nameParts[1];

            if (prefix) {
                prefix = normalize(prefix, parentName, applyMap);
                pluginModule = getOwn(defined, prefix);
            }

            //Account for relative paths if there is a base name.
            if (name) {
                if (prefix) {
                    if (pluginModule && pluginModule.normalize) {
                        //Plugin is loaded, use its normalize method.
                        normalizedName = pluginModule.normalize(name, function (name) {
                            return normalize(name, parentName, applyMap);
                        });
                    } else {
                        // If nested plugin references, then do not try to
                        // normalize, as it will not normalize correctly. This
                        // places a restriction on resourceIds, and the longer
                        // term solution is not to normalize until plugins are
                        // loaded and all normalizations to allow for async
                        // loading of a loader plugin. But for now, fixes the
                        // common uses. Details in #1131
                        normalizedName = name.indexOf('!') === -1 ?
                                         normalize(name, parentName, applyMap) :
                                         name;
                    }
                } else {
                    //A regular module.
                    normalizedName = normalize(name, parentName, applyMap);

                    //Normalized name may be a plugin ID due to map config
                    //application in normalize. The map config values must
                    //already be normalized, so do not need to redo that part.
                    nameParts = splitPrefix(normalizedName);
                    prefix = nameParts[0];
                    normalizedName = nameParts[1];
                    isNormalized = true;

                    url = context.nameToUrl(normalizedName);
                }
            }

            //If the id is a plugin id that cannot be determined if it needs
            //normalization, stamp it with a unique ID so two matching relative
            //ids that may conflict can be separate.
            suffix = prefix && !pluginModule && !isNormalized ?
                     '_unnormalized' + (unnormalizedCounter += 1) :
                     '';

            return {
                prefix: prefix,
                name: normalizedName,
                parentMap: parentModuleMap,
                unnormalized: !!suffix,
                url: url,
                originalName: originalName,
                isDefine: isDefine,
                id: (prefix ?
                        prefix + '!' + normalizedName :
                        normalizedName) + suffix
            };
        }

        function getModule(depMap) {
            var id = depMap.id,
                mod = getOwn(registry, id);

            if (!mod) {
                mod = registry[id] = new context.Module(depMap);
            }

            return mod;
        }

        function on(depMap, name, fn) {
            var id = depMap.id,
                mod = getOwn(registry, id);

            if (hasProp(defined, id) &&
                    (!mod || mod.defineEmitComplete)) {
                if (name === 'defined') {
                    fn(defined[id]);
                }
            } else {
                mod = getModule(depMap);
                if (mod.error && name === 'error') {
                    fn(mod.error);
                } else {
                    mod.on(name, fn);
                }
            }
        }

        function onError(err, errback) {
            var ids = err.requireModules,
                notified = false;

            if (errback) {
                errback(err);
            } else {
                each(ids, function (id) {
                    var mod = getOwn(registry, id);
                    if (mod) {
                        //Set error on module, so it skips timeout checks.
                        mod.error = err;
                        if (mod.events.error) {
                            notified = true;
                            mod.emit('error', err);
                        }
                    }
                });

                if (!notified) {
                    req.onError(err);
                }
            }
        }

        /**
         * Internal method to transfer globalQueue items to this context's
         * defQueue.
         */
        function takeGlobalQueue() {
            //Push all the globalDefQueue items into the context's defQueue
            if (globalDefQueue.length) {
                //Array splice in the values since the context code has a
                //local var ref to defQueue, so cannot just reassign the one
                //on context.
                apsp.apply(defQueue,
                           [defQueue.length, 0].concat(globalDefQueue));
                globalDefQueue = [];
            }
        }

        handlers = {
            'require': function (mod) {
                if (mod.require) {
                    return mod.require;
                } else {
                    return (mod.require = context.makeRequire(mod.map));
                }
            },
            'exports': function (mod) {
                mod.usingExports = true;
                if (mod.map.isDefine) {
                    if (mod.exports) {
                        return (defined[mod.map.id] = mod.exports);
                    } else {
                        return (mod.exports = defined[mod.map.id] = {});
                    }
                }
            },
            'module': function (mod) {
                if (mod.module) {
                    return mod.module;
                } else {
                    return (mod.module = {
                        id: mod.map.id,
                        uri: mod.map.url,
                        config: function () {
                            return  getOwn(config.config, mod.map.id) || {};
                        },
                        exports: mod.exports || (mod.exports = {})
                    });
                }
            }
        };

        function cleanRegistry(id) {
            //Clean up machinery used for waiting modules.
            delete registry[id];
            delete enabledRegistry[id];
        }

        function breakCycle(mod, traced, processed) {
            var id = mod.map.id;

            if (mod.error) {
                mod.emit('error', mod.error);
            } else {
                traced[id] = true;
                each(mod.depMaps, function (depMap, i) {
                    var depId = depMap.id,
                        dep = getOwn(registry, depId);

                    //Only force things that have not completed
                    //being defined, so still in the registry,
                    //and only if it has not been matched up
                    //in the module already.
                    if (dep && !mod.depMatched[i] && !processed[depId]) {
                        if (getOwn(traced, depId)) {
                            mod.defineDep(i, defined[depId]);
                            mod.check(); //pass false?
                        } else {
                            breakCycle(dep, traced, processed);
                        }
                    }
                });
                processed[id] = true;
            }
        }

        function checkLoaded() {
            var err, usingPathFallback,
                waitInterval = config.waitSeconds * 1000,
                //It is possible to disable the wait interval by using waitSeconds of 0.
                expired = waitInterval && (context.startTime + waitInterval) < new Date().getTime(),
                noLoads = [],
                reqCalls = [],
                stillLoading = false,
                needCycleCheck = true;

            //Do not bother if this call was a result of a cycle break.
            if (inCheckLoaded) {
                return;
            }

            inCheckLoaded = true;

            //Figure out the state of all the modules.
            eachProp(enabledRegistry, function (mod) {
                var map = mod.map,
                    modId = map.id;

                //Skip things that are not enabled or in error state.
                if (!mod.enabled) {
                    return;
                }

                if (!map.isDefine) {
                    reqCalls.push(mod);
                }

                if (!mod.error) {
                    //If the module should be executed, and it has not
                    //been inited and time is up, remember it.
                    if (!mod.inited && expired) {
                        if (hasPathFallback(modId)) {
                            usingPathFallback = true;
                            stillLoading = true;
                        } else {
                            noLoads.push(modId);
                            removeScript(modId);
                        }
                    } else if (!mod.inited && mod.fetched && map.isDefine) {
                        stillLoading = true;
                        if (!map.prefix) {
                            //No reason to keep looking for unfinished
                            //loading. If the only stillLoading is a
                            //plugin resource though, keep going,
                            //because it may be that a plugin resource
                            //is waiting on a non-plugin cycle.
                            return (needCycleCheck = false);
                        }
                    }
                }
            });

            if (expired && noLoads.length) {
                //If wait time expired, throw error of unloaded modules.
                err = makeError('timeout', 'Load timeout for modules: ' + noLoads, null, noLoads);
                err.contextName = context.contextName;
                return onError(err);
            }

            //Not expired, check for a cycle.
            if (needCycleCheck) {
                each(reqCalls, function (mod) {
                    breakCycle(mod, {}, {});
                });
            }

            //If still waiting on loads, and the waiting load is something
            //other than a plugin resource, or there are still outstanding
            //scripts, then just try back later.
            if ((!expired || usingPathFallback) && stillLoading) {
                //Something is still waiting to load. Wait for it, but only
                //if a timeout is not already in effect.
                if ((isBrowser || isWebWorker) && !checkLoadedTimeoutId) {
                    checkLoadedTimeoutId = setTimeout(function () {
                        checkLoadedTimeoutId = 0;
                        checkLoaded();
                    }, 50);
                }
            }

            inCheckLoaded = false;
        }

        Module = function (map) {
            this.events = getOwn(undefEvents, map.id) || {};
            this.map = map;
            this.shim = getOwn(config.shim, map.id);
            this.depExports = [];
            this.depMaps = [];
            this.depMatched = [];
            this.pluginMaps = {};
            this.depCount = 0;

            /* this.exports this.factory
               this.depMaps = [],
               this.enabled, this.fetched
            */
        };

        Module.prototype = {
            init: function (depMaps, factory, errback, options) {
                options = options || {};

                //Do not do more inits if already done. Can happen if there
                //are multiple define calls for the same module. That is not
                //a normal, common case, but it is also not unexpected.
                if (this.inited) {
                    return;
                }

                this.factory = factory;

                if (errback) {
                    //Register for errors on this module.
                    this.on('error', errback);
                } else if (this.events.error) {
                    //If no errback already, but there are error listeners
                    //on this module, set up an errback to pass to the deps.
                    errback = bind(this, function (err) {
                        this.emit('error', err);
                    });
                }

                //Do a copy of the dependency array, so that
                //source inputs are not modified. For example
                //"shim" deps are passed in here directly, and
                //doing a direct modification of the depMaps array
                //would affect that config.
                this.depMaps = depMaps && depMaps.slice(0);

                this.errback = errback;

                //Indicate this module has be initialized
                this.inited = true;

                this.ignore = options.ignore;

                //Could have option to init this module in enabled mode,
                //or could have been previously marked as enabled. However,
                //the dependencies are not known until init is called. So
                //if enabled previously, now trigger dependencies as enabled.
                if (options.enabled || this.enabled) {
                    //Enable this module and dependencies.
                    //Will call this.check()
                    this.enable();
                } else {
                    this.check();
                }
            },

            defineDep: function (i, depExports) {
                //Because of cycles, defined callback for a given
                //export can be called more than once.
                if (!this.depMatched[i]) {
                    this.depMatched[i] = true;
                    this.depCount -= 1;
                    this.depExports[i] = depExports;
                }
            },

            fetch: function () {
                if (this.fetched) {
                    return;
                }
                this.fetched = true;

                context.startTime = (new Date()).getTime();

                var map = this.map;

                //If the manager is for a plugin managed resource,
                //ask the plugin to load it now.
                if (this.shim) {
                    context.makeRequire(this.map, {
                        enableBuildCallback: true
                    })(this.shim.deps || [], bind(this, function () {
                        return map.prefix ? this.callPlugin() : this.load();
                    }));
                } else {
                    //Regular dependency.
                    return map.prefix ? this.callPlugin() : this.load();
                }
            },

            load: function () {
                var url = this.map.url;

                //Regular dependency.
                if (!urlFetched[url]) {
                    urlFetched[url] = true;
                    context.load(this.map.id, url);
                }
            },

            /**
             * Checks if the module is ready to define itself, and if so,
             * define it.
             */
            check: function () {
                if (!this.enabled || this.enabling) {
                    return;
                }

                var err, cjsModule,
                    id = this.map.id,
                    depExports = this.depExports,
                    exports = this.exports,
                    factory = this.factory;

                if (!this.inited) {
                    this.fetch();
                } else if (this.error) {
                    this.emit('error', this.error);
                } else if (!this.defining) {
                    //The factory could trigger another require call
                    //that would result in checking this module to
                    //define itself again. If already in the process
                    //of doing that, skip this work.
                    this.defining = true;

                    if (this.depCount < 1 && !this.defined) {
                        if (isFunction(factory)) {
                            //If there is an error listener, favor passing
                            //to that instead of throwing an error. However,
                            //only do it for define()'d  modules. require
                            //errbacks should not be called for failures in
                            //their callbacks (#699). However if a global
                            //onError is set, use that.
                            if ((this.events.error && this.map.isDefine) ||
                                req.onError !== defaultOnError) {
                                try {
                                    exports = context.execCb(id, factory, depExports, exports);
                                } catch (e) {
                                    err = e;
                                }
                            } else {
                                exports = context.execCb(id, factory, depExports, exports);
                            }

                            // Favor return value over exports. If node/cjs in play,
                            // then will not have a return value anyway. Favor
                            // module.exports assignment over exports object.
                            if (this.map.isDefine && exports === undefined) {
                                cjsModule = this.module;
                                if (cjsModule) {
                                    exports = cjsModule.exports;
                                } else if (this.usingExports) {
                                    //exports already set the defined value.
                                    exports = this.exports;
                                }
                            }

                            if (err) {
                                err.requireMap = this.map;
                                err.requireModules = this.map.isDefine ? [this.map.id] : null;
                                err.requireType = this.map.isDefine ? 'define' : 'require';
                                return onError((this.error = err));
                            }

                        } else {
                            //Just a literal value
                            exports = factory;
                        }

                        this.exports = exports;

                        if (this.map.isDefine && !this.ignore) {
                            defined[id] = exports;

                            if (req.onResourceLoad) {
                                req.onResourceLoad(context, this.map, this.depMaps);
                            }
                        }

                        //Clean up
                        cleanRegistry(id);

                        this.defined = true;
                    }

                    //Finished the define stage. Allow calling check again
                    //to allow define notifications below in the case of a
                    //cycle.
                    this.defining = false;

                    if (this.defined && !this.defineEmitted) {
                        this.defineEmitted = true;
                        this.emit('defined', this.exports);
                        this.defineEmitComplete = true;
                    }

                }
            },

            callPlugin: function () {
                var map = this.map,
                    id = map.id,
                    //Map already normalized the prefix.
                    pluginMap = makeModuleMap(map.prefix);

                //Mark this as a dependency for this plugin, so it
                //can be traced for cycles.
                this.depMaps.push(pluginMap);

                on(pluginMap, 'defined', bind(this, function (plugin) {
                    var load, normalizedMap, normalizedMod,
                        bundleId = getOwn(bundlesMap, this.map.id),
                        name = this.map.name,
                        parentName = this.map.parentMap ? this.map.parentMap.name : null,
                        localRequire = context.makeRequire(map.parentMap, {
                            enableBuildCallback: true
                        });

                    //If current map is not normalized, wait for that
                    //normalized name to load instead of continuing.
                    if (this.map.unnormalized) {
                        //Normalize the ID if the plugin allows it.
                        if (plugin.normalize) {
                            name = plugin.normalize(name, function (name) {
                                return normalize(name, parentName, true);
                            }) || '';
                        }

                        //prefix and name should already be normalized, no need
                        //for applying map config again either.
                        normalizedMap = makeModuleMap(map.prefix + '!' + name,
                                                      this.map.parentMap);
                        on(normalizedMap,
                            'defined', bind(this, function (value) {
                                this.init([], function () { return value; }, null, {
                                    enabled: true,
                                    ignore: true
                                });
                            }));

                        normalizedMod = getOwn(registry, normalizedMap.id);
                        if (normalizedMod) {
                            //Mark this as a dependency for this plugin, so it
                            //can be traced for cycles.
                            this.depMaps.push(normalizedMap);

                            if (this.events.error) {
                                normalizedMod.on('error', bind(this, function (err) {
                                    this.emit('error', err);
                                }));
                            }
                            normalizedMod.enable();
                        }

                        return;
                    }

                    //If a paths config, then just load that file instead to
                    //resolve the plugin, as it is built into that paths layer.
                    if (bundleId) {
                        this.map.url = context.nameToUrl(bundleId);
                        this.load();
                        return;
                    }

                    load = bind(this, function (value) {
                        this.init([], function () { return value; }, null, {
                            enabled: true
                        });
                    });

                    load.error = bind(this, function (err) {
                        this.inited = true;
                        this.error = err;
                        err.requireModules = [id];

                        //Remove temp unnormalized modules for this module,
                        //since they will never be resolved otherwise now.
                        eachProp(registry, function (mod) {
                            if (mod.map.id.indexOf(id + '_unnormalized') === 0) {
                                cleanRegistry(mod.map.id);
                            }
                        });

                        onError(err);
                    });

                    //Allow plugins to load other code without having to know the
                    //context or how to 'complete' the load.
                    load.fromText = bind(this, function (text, textAlt) {
                        /*jslint evil: true */
                        var moduleName = map.name,
                            moduleMap = makeModuleMap(moduleName),
                            hasInteractive = useInteractive;

                        //As of 2.1.0, support just passing the text, to reinforce
                        //fromText only being called once per resource. Still
                        //support old style of passing moduleName but discard
                        //that moduleName in favor of the internal ref.
                        if (textAlt) {
                            text = textAlt;
                        }

                        //Turn off interactive script matching for IE for any define
                        //calls in the text, then turn it back on at the end.
                        if (hasInteractive) {
                            useInteractive = false;
                        }

                        //Prime the system by creating a module instance for
                        //it.
                        getModule(moduleMap);

                        //Transfer any config to this other module.
                        if (hasProp(config.config, id)) {
                            config.config[moduleName] = config.config[id];
                        }

                        try {
                            req.exec(text);
                        } catch (e) {
                            return onError(makeError('fromtexteval',
                                             'fromText eval for ' + id +
                                            ' failed: ' + e,
                                             e,
                                             [id]));
                        }

                        if (hasInteractive) {
                            useInteractive = true;
                        }

                        //Mark this as a dependency for the plugin
                        //resource
                        this.depMaps.push(moduleMap);

                        //Support anonymous modules.
                        context.completeLoad(moduleName);

                        //Bind the value of that module to the value for this
                        //resource ID.
                        localRequire([moduleName], load);
                    });

                    //Use parentName here since the plugin's name is not reliable,
                    //could be some weird string with no path that actually wants to
                    //reference the parentName's path.
                    plugin.load(map.name, localRequire, load, config);
                }));

                context.enable(pluginMap, this);
                this.pluginMaps[pluginMap.id] = pluginMap;
            },

            enable: function () {
                enabledRegistry[this.map.id] = this;
                this.enabled = true;

                //Set flag mentioning that the module is enabling,
                //so that immediate calls to the defined callbacks
                //for dependencies do not trigger inadvertent load
                //with the depCount still being zero.
                this.enabling = true;

                //Enable each dependency
                each(this.depMaps, bind(this, function (depMap, i) {
                    var id, mod, handler;

                    if (typeof depMap === 'string') {
                        //Dependency needs to be converted to a depMap
                        //and wired up to this module.
                        depMap = makeModuleMap(depMap,
                                               (this.map.isDefine ? this.map : this.map.parentMap),
                                               false,
                                               !this.skipMap);
                        this.depMaps[i] = depMap;

                        handler = getOwn(handlers, depMap.id);

                        if (handler) {
                            this.depExports[i] = handler(this);
                            return;
                        }

                        this.depCount += 1;

                        on(depMap, 'defined', bind(this, function (depExports) {
                            this.defineDep(i, depExports);
                            this.check();
                        }));

                        if (this.errback) {
                            on(depMap, 'error', bind(this, this.errback));
                        } else if (this.events.error) {
                            // No direct errback on this module, but something
                            // else is listening for errors, so be sure to
                            // propagate the error correctly.
                            on(depMap, 'error', bind(this, function(err) {
                                this.emit('error', err);
                            }));
                        }
                    }

                    id = depMap.id;
                    mod = registry[id];

                    //Skip special modules like 'require', 'exports', 'module'
                    //Also, don't call enable if it is already enabled,
                    //important in circular dependency cases.
                    if (!hasProp(handlers, id) && mod && !mod.enabled) {
                        context.enable(depMap, this);
                    }
                }));

                //Enable each plugin that is used in
                //a dependency
                eachProp(this.pluginMaps, bind(this, function (pluginMap) {
                    var mod = getOwn(registry, pluginMap.id);
                    if (mod && !mod.enabled) {
                        context.enable(pluginMap, this);
                    }
                }));

                this.enabling = false;

                this.check();
            },

            on: function (name, cb) {
                var cbs = this.events[name];
                if (!cbs) {
                    cbs = this.events[name] = [];
                }
                cbs.push(cb);
            },

            emit: function (name, evt) {
                each(this.events[name], function (cb) {
                    cb(evt);
                });
                if (name === 'error') {
                    //Now that the error handler was triggered, remove
                    //the listeners, since this broken Module instance
                    //can stay around for a while in the registry.
                    delete this.events[name];
                }
            }
        };

        function callGetModule(args) {
            //Skip modules already defined.
            if (!hasProp(defined, args[0])) {
                getModule(makeModuleMap(args[0], null, true)).init(args[1], args[2]);
            }
        }

        function removeListener(node, func, name, ieName) {
            //Favor detachEvent because of IE9
            //issue, see attachEvent/addEventListener comment elsewhere
            //in this file.
            if (node.detachEvent && !isOpera) {
                //Probably IE. If not it will throw an error, which will be
                //useful to know.
                if (ieName) {
                    node.detachEvent(ieName, func);
                }
            } else {
                node.removeEventListener(name, func, false);
            }
        }

        /**
         * Given an event from a script node, get the requirejs info from it,
         * and then removes the event listeners on the node.
         * @param {Event} evt
         * @returns {Object}
         */
        function getScriptData(evt) {
            //Using currentTarget instead of target for Firefox 2.0's sake. Not
            //all old browsers will be supported, but this one was easy enough
            //to support and still makes sense.
            var node = evt.currentTarget || evt.srcElement;

            //Remove the listeners once here.
            removeListener(node, context.onScriptLoad, 'load', 'onreadystatechange');
            removeListener(node, context.onScriptError, 'error');

            return {
                node: node,
                id: node && node.getAttribute('data-requiremodule')
            };
        }

        function intakeDefines() {
            var args;

            //Any defined modules in the global queue, intake them now.
            takeGlobalQueue();

            //Make sure any remaining defQueue items get properly processed.
            while (defQueue.length) {
                args = defQueue.shift();
                if (args[0] === null) {
                    return onError(makeError('mismatch', 'Mismatched anonymous define() module: ' + args[args.length - 1]));
                } else {
                    //args are id, deps, factory. Should be normalized by the
                    //define() function.
                    callGetModule(args);
                }
            }
        }

        context = {
            config: config,
            contextName: contextName,
            registry: registry,
            defined: defined,
            urlFetched: urlFetched,
            defQueue: defQueue,
            Module: Module,
            makeModuleMap: makeModuleMap,
            nextTick: req.nextTick,
            onError: onError,

            /**
             * Set a configuration for the context.
             * @param {Object} cfg config object to integrate.
             */
            configure: function (cfg) {
                //Make sure the baseUrl ends in a slash.
                if (cfg.baseUrl) {
                    if (cfg.baseUrl.charAt(cfg.baseUrl.length - 1) !== '/') {
                        cfg.baseUrl += '/';
                    }
                }

                //Save off the paths since they require special processing,
                //they are additive.
                var shim = config.shim,
                    objs = {
                        paths: true,
                        bundles: true,
                        config: true,
                        map: true
                    };

                eachProp(cfg, function (value, prop) {
                    if (objs[prop]) {
                        if (!config[prop]) {
                            config[prop] = {};
                        }
                        mixin(config[prop], value, true, true);
                    } else {
                        config[prop] = value;
                    }
                });

                //Reverse map the bundles
                if (cfg.bundles) {
                    eachProp(cfg.bundles, function (value, prop) {
                        each(value, function (v) {
                            if (v !== prop) {
                                bundlesMap[v] = prop;
                            }
                        });
                    });
                }

                //Merge shim
                if (cfg.shim) {
                    eachProp(cfg.shim, function (value, id) {
                        //Normalize the structure
                        if (isArray(value)) {
                            value = {
                                deps: value
                            };
                        }
                        if ((value.exports || value.init) && !value.exportsFn) {
                            value.exportsFn = context.makeShimExports(value);
                        }
                        shim[id] = value;
                    });
                    config.shim = shim;
                }

                //Adjust packages if necessary.
                if (cfg.packages) {
                    each(cfg.packages, function (pkgObj) {
                        var location, name;

                        pkgObj = typeof pkgObj === 'string' ? { name: pkgObj } : pkgObj;

                        name = pkgObj.name;
                        location = pkgObj.location;
                        if (location) {
                            config.paths[name] = pkgObj.location;
                        }

                        //Save pointer to main module ID for pkg name.
                        //Remove leading dot in main, so main paths are normalized,
                        //and remove any trailing .js, since different package
                        //envs have different conventions: some use a module name,
                        //some use a file name.
                        config.pkgs[name] = pkgObj.name + '/' + (pkgObj.main || 'main')
                                     .replace(currDirRegExp, '')
                                     .replace(jsSuffixRegExp, '');
                    });
                }

                //If there are any "waiting to execute" modules in the registry,
                //update the maps for them, since their info, like URLs to load,
                //may have changed.
                eachProp(registry, function (mod, id) {
                    //If module already has init called, since it is too
                    //late to modify them, and ignore unnormalized ones
                    //since they are transient.
                    if (!mod.inited && !mod.map.unnormalized) {
                        mod.map = makeModuleMap(id);
                    }
                });

                //If a deps array or a config callback is specified, then call
                //require with those args. This is useful when require is defined as a
                //config object before require.js is loaded.
                if (cfg.deps || cfg.callback) {
                    context.require(cfg.deps || [], cfg.callback);
                }
            },

            makeShimExports: function (value) {
                function fn() {
                    var ret;
                    if (value.init) {
                        ret = value.init.apply(global, arguments);
                    }
                    return ret || (value.exports && getGlobal(value.exports));
                }
                return fn;
            },

            makeRequire: function (relMap, options) {
                options = options || {};

                function localRequire(deps, callback, errback) {
                    var id, map, requireMod;

                    if (options.enableBuildCallback && callback && isFunction(callback)) {
                        callback.__requireJsBuild = true;
                    }

                    if (typeof deps === 'string') {
                        if (isFunction(callback)) {
                            //Invalid call
                            return onError(makeError('requireargs', 'Invalid require call'), errback);
                        }

                        //If require|exports|module are requested, get the
                        //value for them from the special handlers. Caveat:
                        //this only works while module is being defined.
                        if (relMap && hasProp(handlers, deps)) {
                            return handlers[deps](registry[relMap.id]);
                        }

                        //Synchronous access to one module. If require.get is
                        //available (as in the Node adapter), prefer that.
                        if (req.get) {
                            return req.get(context, deps, relMap, localRequire);
                        }

                        //Normalize module name, if it contains . or ..
                        map = makeModuleMap(deps, relMap, false, true);
                        id = map.id;

                        if (!hasProp(defined, id)) {
                            return onError(makeError('notloaded', 'Module name "' +
                                        id +
                                        '" has not been loaded yet for context: ' +
                                        contextName +
                                        (relMap ? '' : '. Use require([])')));
                        }
                        return defined[id];
                    }

                    //Grab defines waiting in the global queue.
                    intakeDefines();

                    //Mark all the dependencies as needing to be loaded.
                    context.nextTick(function () {
                        //Some defines could have been added since the
                        //require call, collect them.
                        intakeDefines();

                        requireMod = getModule(makeModuleMap(null, relMap));

                        //Store if map config should be applied to this require
                        //call for dependencies.
                        requireMod.skipMap = options.skipMap;

                        requireMod.init(deps, callback, errback, {
                            enabled: true
                        });

                        checkLoaded();
                    });

                    return localRequire;
                }

                mixin(localRequire, {
                    isBrowser: isBrowser,

                    /**
                     * Converts a module name + .extension into an URL path.
                     * *Requires* the use of a module name. It does not support using
                     * plain URLs like nameToUrl.
                     */
                    toUrl: function (moduleNamePlusExt) {
                        var ext,
                            index = moduleNamePlusExt.lastIndexOf('.'),
                            segment = moduleNamePlusExt.split('/')[0],
                            isRelative = segment === '.' || segment === '..';

                        //Have a file extension alias, and it is not the
                        //dots from a relative path.
                        if (index !== -1 && (!isRelative || index > 1)) {
                            ext = moduleNamePlusExt.substring(index, moduleNamePlusExt.length);
                            moduleNamePlusExt = moduleNamePlusExt.substring(0, index);
                        }

                        return context.nameToUrl(normalize(moduleNamePlusExt,
                                                relMap && relMap.id, true), ext,  true);
                    },

                    defined: function (id) {
                        return hasProp(defined, makeModuleMap(id, relMap, false, true).id);
                    },

                    specified: function (id) {
                        id = makeModuleMap(id, relMap, false, true).id;
                        return hasProp(defined, id) || hasProp(registry, id);
                    }
                });

                //Only allow undef on top level require calls
                if (!relMap) {
                    localRequire.undef = function (id) {
                        //Bind any waiting define() calls to this context,
                        //fix for #408
                        takeGlobalQueue();

                        var map = makeModuleMap(id, relMap, true),
                            mod = getOwn(registry, id);

                        removeScript(id);

                        delete defined[id];
                        delete urlFetched[map.url];
                        delete undefEvents[id];

                        //Clean queued defines too. Go backwards
                        //in array so that the splices do not
                        //mess up the iteration.
                        eachReverse(defQueue, function(args, i) {
                            if(args[0] === id) {
                                defQueue.splice(i, 1);
                            }
                        });

                        if (mod) {
                            //Hold on to listeners in case the
                            //module will be attempted to be reloaded
                            //using a different config.
                            if (mod.events.defined) {
                                undefEvents[id] = mod.events;
                            }

                            cleanRegistry(id);
                        }
                    };
                }

                return localRequire;
            },

            /**
             * Called to enable a module if it is still in the registry
             * awaiting enablement. A second arg, parent, the parent module,
             * is passed in for context, when this method is overridden by
             * the optimizer. Not shown here to keep code compact.
             */
            enable: function (depMap) {
                var mod = getOwn(registry, depMap.id);
                if (mod) {
                    getModule(depMap).enable();
                }
            },

            /**
             * Internal method used by environment adapters to complete a load event.
             * A load event could be a script load or just a load pass from a synchronous
             * load call.
             * @param {String} moduleName the name of the module to potentially complete.
             */
            completeLoad: function (moduleName) {
                var found, args, mod,
                    shim = getOwn(config.shim, moduleName) || {},
                    shExports = shim.exports;

                takeGlobalQueue();

                while (defQueue.length) {
                    args = defQueue.shift();
                    if (args[0] === null) {
                        args[0] = moduleName;
                        //If already found an anonymous module and bound it
                        //to this name, then this is some other anon module
                        //waiting for its completeLoad to fire.
                        if (found) {
                            break;
                        }
                        found = true;
                    } else if (args[0] === moduleName) {
                        //Found matching define call for this script!
                        found = true;
                    }

                    callGetModule(args);
                }

                //Do this after the cycle of callGetModule in case the result
                //of those calls/init calls changes the registry.
                mod = getOwn(registry, moduleName);

                if (!found && !hasProp(defined, moduleName) && mod && !mod.inited) {
                    if (config.enforceDefine && (!shExports || !getGlobal(shExports))) {
                        if (hasPathFallback(moduleName)) {
                            return;
                        } else {
                            return onError(makeError('nodefine',
                                             'No define call for ' + moduleName,
                                             null,
                                             [moduleName]));
                        }
                    } else {
                        //A script that does not call define(), so just simulate
                        //the call for it.
                        callGetModule([moduleName, (shim.deps || []), shim.exportsFn]);
                    }
                }

                checkLoaded();
            },

            /**
             * Converts a module name to a file path. Supports cases where
             * moduleName may actually be just an URL.
             * Note that it **does not** call normalize on the moduleName,
             * it is assumed to have already been normalized. This is an
             * internal API, not a public one. Use toUrl for the public API.
             */
            nameToUrl: function (moduleName, ext, skipExt) {
                var paths, syms, i, parentModule, url,
                    parentPath, bundleId,
                    pkgMain = getOwn(config.pkgs, moduleName);

                if (pkgMain) {
                    moduleName = pkgMain;
                }

                bundleId = getOwn(bundlesMap, moduleName);

                if (bundleId) {
                    return context.nameToUrl(bundleId, ext, skipExt);
                }

                //If a colon is in the URL, it indicates a protocol is used and it is just
                //an URL to a file, or if it starts with a slash, contains a query arg (i.e. ?)
                //or ends with .js, then assume the user meant to use an url and not a module id.
                //The slash is important for protocol-less URLs as well as full paths.
                if (req.jsExtRegExp.test(moduleName)) {
                    //Just a plain path, not module name lookup, so just return it.
                    //Add extension if it is included. This is a bit wonky, only non-.js things pass
                    //an extension, this method probably needs to be reworked.
                    url = moduleName + (ext || '');
                } else {
                    //A module that needs to be converted to a path.
                    paths = config.paths;

                    syms = moduleName.split('/');
                    //For each module name segment, see if there is a path
                    //registered for it. Start with most specific name
                    //and work up from it.
                    for (i = syms.length; i > 0; i -= 1) {
                        parentModule = syms.slice(0, i).join('/');

                        parentPath = getOwn(paths, parentModule);
                        if (parentPath) {
                            //If an array, it means there are a few choices,
                            //Choose the one that is desired
                            if (isArray(parentPath)) {
                                parentPath = parentPath[0];
                            }
                            syms.splice(0, i, parentPath);
                            break;
                        }
                    }

                    //Join the path parts together, then figure out if baseUrl is needed.
                    url = syms.join('/');
                    url += (ext || (/^data\:|\?/.test(url) || skipExt ? '' : '.js'));
                    url = (url.charAt(0) === '/' || url.match(/^[\w\+\.\-]+:/) ? '' : config.baseUrl) + url;
                }

                return config.urlArgs ? url +
                                        ((url.indexOf('?') === -1 ? '?' : '&') +
                                         config.urlArgs) : url;
            },

            //Delegates to req.load. Broken out as a separate function to
            //allow overriding in the optimizer.
            load: function (id, url) {
                req.load(context, id, url);
            },

            /**
             * Executes a module callback function. Broken out as a separate function
             * solely to allow the build system to sequence the files in the built
             * layer in the right sequence.
             *
             * @private
             */
            execCb: function (name, callback, args, exports) {
                return callback.apply(exports, args);
            },

            /**
             * callback for script loads, used to check status of loading.
             *
             * @param {Event} evt the event from the browser for the script
             * that was loaded.
             */
            onScriptLoad: function (evt) {
                //Using currentTarget instead of target for Firefox 2.0's sake. Not
                //all old browsers will be supported, but this one was easy enough
                //to support and still makes sense.
                if (evt.type === 'load' ||
                        (readyRegExp.test((evt.currentTarget || evt.srcElement).readyState))) {
                    //Reset interactive script so a script node is not held onto for
                    //to long.
                    interactiveScript = null;

                    //Pull out the name of the module and the context.
                    var data = getScriptData(evt);
                    context.completeLoad(data.id);
                }
            },

            /**
             * Callback for script errors.
             */
            onScriptError: function (evt) {
                var data = getScriptData(evt);
                if (!hasPathFallback(data.id)) {
                    return onError(makeError('scripterror', 'Script error for: ' + data.id, evt, [data.id]));
                }
            }
        };

        context.require = context.makeRequire();
        return context;
    }

    /**
     * Main entry point.
     *
     * If the only argument to require is a string, then the module that
     * is represented by that string is fetched for the appropriate context.
     *
     * If the first argument is an array, then it will be treated as an array
     * of dependency string names to fetch. An optional function callback can
     * be specified to execute when all of those dependencies are available.
     *
     * Make a local req variable to help Caja compliance (it assumes things
     * on a require that are not standardized), and to give a short
     * name for minification/local scope use.
     */
    req = requirejs = function (deps, callback, errback, optional) {

        //Find the right context, use default
        var context, config,
            contextName = defContextName;

        // Determine if have config object in the call.
        if (!isArray(deps) && typeof deps !== 'string') {
            // deps is a config object
            config = deps;
            if (isArray(callback)) {
                // Adjust args if there are dependencies
                deps = callback;
                callback = errback;
                errback = optional;
            } else {
                deps = [];
            }
        }

        if (config && config.context) {
            contextName = config.context;
        }

        context = getOwn(contexts, contextName);
        if (!context) {
            context = contexts[contextName] = req.s.newContext(contextName);
        }

        if (config) {
            context.configure(config);
        }

        return context.require(deps, callback, errback);
    };

    /**
     * Support require.config() to make it easier to cooperate with other
     * AMD loaders on globally agreed names.
     */
    req.config = function (config) {
        return req(config);
    };

    /**
     * Execute something after the current tick
     * of the event loop. Override for other envs
     * that have a better solution than setTimeout.
     * @param  {Function} fn function to execute later.
     */
    req.nextTick = typeof setTimeout !== 'undefined' ? function (fn) {
        setTimeout(fn, 4);
    } : function (fn) { fn(); };

    /**
     * Export require as a global, but only if it does not already exist.
     */
    if (!require) {
        require = req;
    }

    req.version = version;

    //Used to filter out dependencies that are already paths.
    req.jsExtRegExp = /^\/|:|\?|\.js$/;
    req.isBrowser = isBrowser;
    s = req.s = {
        contexts: contexts,
        newContext: newContext
    };

    //Create default context.
    req({});

    //Exports some context-sensitive methods on global require.
    each([
        'toUrl',
        'undef',
        'defined',
        'specified'
    ], function (prop) {
        //Reference from contexts instead of early binding to default context,
        //so that during builds, the latest instance of the default context
        //with its config gets used.
        req[prop] = function () {
            var ctx = contexts[defContextName];
            return ctx.require[prop].apply(ctx, arguments);
        };
    });

    if (isBrowser) {
        head = s.head = document.getElementsByTagName('head')[0];
        //If BASE tag is in play, using appendChild is a problem for IE6.
        //When that browser dies, this can be removed. Details in this jQuery bug:
        //http://dev.jquery.com/ticket/2709
        baseElement = document.getElementsByTagName('base')[0];
        if (baseElement) {
            head = s.head = baseElement.parentNode;
        }
    }

    /**
     * Any errors that require explicitly generates will be passed to this
     * function. Intercept/override it if you want custom error handling.
     * @param {Error} err the error object.
     */
    req.onError = defaultOnError;

    /**
     * Creates the node for the load command. Only used in browser envs.
     */
    req.createNode = function (config, moduleName, url) {
        var node = config.xhtml ?
                document.createElementNS('http://www.w3.org/1999/xhtml', 'html:script') :
                document.createElement('script');
        node.type = config.scriptType || 'text/javascript';
        node.charset = 'utf-8';
        node.async = true;
        return node;
    };

    /**
     * Does the request to load a module for the browser case.
     * Make this a separate function to allow other environments
     * to override it.
     *
     * @param {Object} context the require context to find state.
     * @param {String} moduleName the name of the module.
     * @param {Object} url the URL to the module.
     */
    req.load = function (context, moduleName, url) {
        var config = (context && context.config) || {},
            node;
        if (isBrowser) {
            //In the browser so use a script tag
            node = req.createNode(config, moduleName, url);

            node.setAttribute('data-requirecontext', context.contextName);
            node.setAttribute('data-requiremodule', moduleName);

            //Set up load listener. Test attachEvent first because IE9 has
            //a subtle issue in its addEventListener and script onload firings
            //that do not match the behavior of all other browsers with
            //addEventListener support, which fire the onload event for a
            //script right after the script execution. See:
            //https://connect.microsoft.com/IE/feedback/details/648057/script-onload-event-is-not-fired-immediately-after-script-execution
            //UNFORTUNATELY Opera implements attachEvent but does not follow the script
            //script execution mode.
            if (node.attachEvent &&
                    //Check if node.attachEvent is artificially added by custom script or
                    //natively supported by browser
                    //read https://github.com/jrburke/requirejs/issues/187
                    //if we can NOT find [native code] then it must NOT natively supported.
                    //in IE8, node.attachEvent does not have toString()
                    //Note the test for "[native code" with no closing brace, see:
                    //https://github.com/jrburke/requirejs/issues/273
                    !(node.attachEvent.toString && node.attachEvent.toString().indexOf('[native code') < 0) &&
                    !isOpera) {
                //Probably IE. IE (at least 6-8) do not fire
                //script onload right after executing the script, so
                //we cannot tie the anonymous define call to a name.
                //However, IE reports the script as being in 'interactive'
                //readyState at the time of the define call.
                useInteractive = true;

                node.attachEvent('onreadystatechange', context.onScriptLoad);
                //It would be great to add an error handler here to catch
                //404s in IE9+. However, onreadystatechange will fire before
                //the error handler, so that does not help. If addEventListener
                //is used, then IE will fire error before load, but we cannot
                //use that pathway given the connect.microsoft.com issue
                //mentioned above about not doing the 'script execute,
                //then fire the script load event listener before execute
                //next script' that other browsers do.
                //Best hope: IE10 fixes the issues,
                //and then destroys all installs of IE 6-9.
                //node.attachEvent('onerror', context.onScriptError);
            } else {
                node.addEventListener('load', context.onScriptLoad, false);
                node.addEventListener('error', context.onScriptError, false);
            }
            node.src = url;

            //For some cache cases in IE 6-8, the script executes before the end
            //of the appendChild execution, so to tie an anonymous define
            //call to the module name (which is stored on the node), hold on
            //to a reference to this node, but clear after the DOM insertion.
            currentlyAddingScript = node;
            if (baseElement) {
                head.insertBefore(node, baseElement);
            } else {
                head.appendChild(node);
            }
            currentlyAddingScript = null;

            return node;
        } else if (isWebWorker) {
            try {
                //In a web worker, use importScripts. This is not a very
                //efficient use of importScripts, importScripts will block until
                //its script is downloaded and evaluated. However, if web workers
                //are in play, the expectation that a build has been done so that
                //only one script needs to be loaded anyway. This may need to be
                //reevaluated if other use cases become common.
                importScripts(url);

                //Account for anonymous modules
                context.completeLoad(moduleName);
            } catch (e) {
                context.onError(makeError('importscripts',
                                'importScripts failed for ' +
                                    moduleName + ' at ' + url,
                                e,
                                [moduleName]));
            }
        }
    };

    function getInteractiveScript() {
        if (interactiveScript && interactiveScript.readyState === 'interactive') {
            return interactiveScript;
        }

        eachReverse(scripts(), function (script) {
            if (script.readyState === 'interactive') {
                return (interactiveScript = script);
            }
        });
        return interactiveScript;
    }

    //Look for a data-main script attribute, which could also adjust the baseUrl.
    if (isBrowser && !cfg.skipDataMain) {
        //Figure out baseUrl. Get it from the script tag with require.js in it.
        eachReverse(scripts(), function (script) {
            //Set the 'head' where we can append children by
            //using the script's parent.
            if (!head) {
                head = script.parentNode;
            }

            //Look for a data-main attribute to set main script for the page
            //to load. If it is there, the path to data main becomes the
            //baseUrl, if it is not already set.
            dataMain = script.getAttribute('data-main');
            if (dataMain) {
                //Preserve dataMain in case it is a path (i.e. contains '?')
                mainScript = dataMain;

                //Set final baseUrl if there is not already an explicit one.
                if (!cfg.baseUrl) {
                    //Pull off the directory of data-main for use as the
                    //baseUrl.
                    src = mainScript.split('/');
                    mainScript = src.pop();
                    subPath = src.length ? src.join('/')  + '/' : './';

                    cfg.baseUrl = subPath;
                }

                //Strip off any trailing .js since mainScript is now
                //like a module name.
                mainScript = mainScript.replace(jsSuffixRegExp, '');

                 //If mainScript is still a path, fall back to dataMain
                if (req.jsExtRegExp.test(mainScript)) {
                    mainScript = dataMain;
                }

                //Put the data-main script in the files to load.
                cfg.deps = cfg.deps ? cfg.deps.concat(mainScript) : [mainScript];

                return true;
            }
        });
    }

    /**
     * The function that handles definitions of modules. Differs from
     * require() in that a string for the module should be the first argument,
     * and the function to execute after dependencies are loaded should
     * return a value to define the module corresponding to the first argument's
     * name.
     */
    define = function (name, deps, callback) {
        var node, context;

        //Allow for anonymous modules
        if (typeof name !== 'string') {
            //Adjust args appropriately
            callback = deps;
            deps = name;
            name = null;
        }

        //This module may not have dependencies
        if (!isArray(deps)) {
            callback = deps;
            deps = null;
        }

        //If no name, and callback is a function, then figure out if it a
        //CommonJS thing with dependencies.
        if (!deps && isFunction(callback)) {
            deps = [];
            //Remove comments from the callback string,
            //look for require calls, and pull them into the dependencies,
            //but only if there are function args.
            if (callback.length) {
                callback
                    .toString()
                    .replace(commentRegExp, '')
                    .replace(cjsRequireRegExp, function (match, dep) {
                        deps.push(dep);
                    });

                //May be a CommonJS thing even without require calls, but still
                //could use exports, and module. Avoid doing exports and module
                //work though if it just needs require.
                //REQUIRES the function to expect the CommonJS variables in the
                //order listed below.
                deps = (callback.length === 1 ? ['require'] : ['require', 'exports', 'module']).concat(deps);
            }
        }

        //If in IE 6-8 and hit an anonymous define() call, do the interactive
        //work.
        if (useInteractive) {
            node = currentlyAddingScript || getInteractiveScript();
            if (node) {
                if (!name) {
                    name = node.getAttribute('data-requiremodule');
                }
                context = contexts[node.getAttribute('data-requirecontext')];
            }
        }

        //Always save off evaluating the def call until the script onload handler.
        //This allows multiple modules to be in a file without prematurely
        //tracing dependencies, and allows for anonymous module support,
        //where the module name is not known until the script onload event
        //occurs. If no context, use the global queue, and get it processed
        //in the onscript load callback.
        (context ? context.defQueue : globalDefQueue).push([name, deps, callback]);
    };

    define.amd = {
        jQuery: true
    };


    /**
     * Executes the text. Normally just uses eval, but can be modified
     * to use a better, environment-specific call. Only used for transpiling
     * loader plugins, not for plain JS modules.
     * @param {String} text the text to execute/evaluate.
     */
    req.exec = function (text) {
        /*jslint evil: true */
        return eval(text);
    };

    //Set up with config info.
    req(cfg);
}(this));

/*!
 * jQuery JavaScript Library v2.1.3
 * http://jquery.com/
 *
 * Includes Sizzle.js
 * http://sizzlejs.com/
 *
 * Copyright 2005, 2014 jQuery Foundation, Inc. and other contributors
 * Released under the MIT license
 * http://jquery.org/license
 *
 * Date: 2014-12-18T15:11Z
 */

/*!
 * Sizzle CSS Selector Engine v2.2.0-pre
 * http://sizzlejs.com/
 *
 * Copyright 2008, 2014 jQuery Foundation, Inc. and other contributors
 * Released under the MIT license
 * http://jquery.org/license
 *
 * Date: 2014-12-16
 */

/*! Hammer.JS - v1.0.11 - 2014-05-20
 * http://eightmedia.github.io/hammer.js
 *
 * Copyright (c) 2014 Jorik Tangelder <j.tangelder@gmail.com>;
 * Licensed under the MIT license */

/*! cornerstone - v0.7.3 - 2015-04-04 | (c) 2014 Chris Hafey | https://github.com/chafey/cornerstone */

/*! cornerstoneMath - v0.1.1 - 2015-01-30 | (c) 2014 Chris Hafey | https://github.com/chafey/cornerstoneMath */

/*! cornerstoneTools - v0.6.2 - 2015-04-04 | (c) 2014 Chris Hafey | https://github.com/chafey/cornerstoneTools */

/*! dicom-parser - v1.0.1 - 2015-04-06 | (c) 2014 Chris Hafey | https://github.com/chafey/dicomParser */

/*! cornerstoneWebImageLoader - v0.4.0 - 2015-04-04 | (c) 2014 Chris Hafey | https://github.com/chafey/cornerstoneWebImageLoader */

/* Copyright 2012 Mozilla Foundation
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/*! cornerstone-wado-image-loader - v0.5.2 - 2015-04-04 | (c) 2014 Chris Hafey | https://github.com/chafey/cornerstoneWADOImageLoader */

function info(e){PDFJS.verbosity>=PDFJS.VERBOSITY_LEVELS.infos&&console.log("Info: "+e)}function warn(e){PDFJS.verbosity>=PDFJS.VERBOSITY_LEVELS.warnings&&console.log("Warning: "+e)}function error(e){if(arguments.length>1){var t=["Error:"];t.push.apply(t,arguments),console.log.apply(console,t),e=[].join.call(arguments," ")}else console.log("Error: "+e);throw console.log(backtrace()),UnsupportedManager.notify(UNSUPPORTED_FEATURES.unknown),new Error(e)}function backtrace(){try{throw new Error}catch(e){return e.stack?e.stack.split("\n").slice(2).join("\n"):""}}function assert(e,t){e||error(t)}function combineUrl(e,t){if(!t)return e;if(/^[a-z][a-z0-9+\-.]*:/i.test(t))return t;var n;if(t.charAt(0)==="/")return n=e.indexOf("://"),t.charAt(1)==="/"?++n:n=e.indexOf("/",n+3),e.substring(0,n)+t;var r=e.length;n=e.lastIndexOf("#"),r=n>=0?n:r,n=e.lastIndexOf("?",r),r=n>=0?n:r;var i=e.lastIndexOf("/",r);return e.substring(0,i+1)+t}function isValidUrl(e,t){if(!e)return!1;var n=/^[a-z][a-z0-9+\-.]*(?=:)/i.exec(e);if(!n)return t;n=n[0].toLowerCase();switch(n){case"http":case"https":case"ftp":case"mailto":case"tel":return!0;default:return!1}}function shadow(e,t,n){return Object.defineProperty(e,t,{value:n,enumerable:!0,configurable:!0,writable:!1}),n}function bytesToString(e){assert(e!==null&&typeof e=="object"&&e.length!==undefined,"Invalid argument for bytesToString");var t=e.length,n=8192;if(t<n)return String.fromCharCode.apply(null,e);var r=[];for(var i=0;i<t;i+=n){var s=Math.min(i+n,t),o=e.subarray(i,s);r.push(String.fromCharCode.apply(null,o))}return r.join("")}function stringToBytes(e){assert(typeof e=="string","Invalid argument for stringToBytes");var t=e.length,n=new Uint8Array(t);for(var r=0;r<t;++r)n[r]=e.charCodeAt(r)&255;return n}function string32(e){return String.fromCharCode(e>>24&255,e>>16&255,e>>8&255,e&255)}function log2(e){var t=1,n=0;while(e>t)t<<=1,n++;return n}function readInt8(e,t){return e[t]<<24>>24}function readUint16(e,t){return e[t]<<8|e[t+1]}function readUint32(e,t){return(e[t]<<24|e[t+1]<<16|e[t+2]<<8|e[t+3])>>>0}function isLittleEndian(){var e=new Uint8Array(2);e[0]=1;var t=new Uint16Array(e.buffer);return t[0]===1}function hasCanvasTypedArrays(){var e=document.createElement("canvas");e.width=e.height=1;var t=e.getContext("2d"),n=t.createImageData(1,1);return typeof n.data.buffer!="undefined"}function stringToPDFString(e){var t,n=e.length,r=[];if(e[0]==="þ"&&e[1]==="ÿ")for(t=2;t<n;t+=2)r.push(String.fromCharCode(e.charCodeAt(t)<<8|e.charCodeAt(t+1)));else for(t=0;t<n;++t){var i=PDFStringTranslateTable[e.charCodeAt(t)];r.push(i?String.fromCharCode(i):e.charAt(t))}return r.join("")}function stringToUTF8String(e){return decodeURIComponent(escape(e))}function isEmptyObj(e){for(var t in e)return!1;return!0}function isBool(e){return typeof e=="boolean"}function isInt(e){return typeof e=="number"&&(e|0)===e}function isNum(e){return typeof e=="number"}function isString(e){return typeof e=="string"}function isNull(e){return e===null}function isName(e){return e instanceof Name}function isCmd(e,t){return e instanceof Cmd&&(t===undefined||e.cmd===t)}function isDict(e,t){if(e instanceof Dict){if(!t)return!0;var n=e.get("Type");return isName(n)&&n.name===t}return!1}function isArray(e){return e instanceof Array}function isStream(e){return typeof e=="object"&&e!==null&&e.getBytes!==undefined}function isArrayBuffer(e){return typeof e=="object"&&e!==null&&e.byteLength!==undefined}function isRef(e){return e instanceof Ref}function createPromiseCapability(){var e={};return e.promise=new Promise(function(t,n){e.resolve=t,e.reject=n}),e}function MessageHandler(e,t){this.name=e,this.comObj=t,this.callbackIndex=1,this.postMessageTransfers=!0;var n=this.callbacksCapabilities={},r=this.actionHandler={};r.console_log=[function(t){console.log.apply(console,t)}],r.console_error=[function(t){console.error.apply(console,t)}],r._unsupported_feature=[function(t){UnsupportedManager.notify(t)}],t.onmessage=function(i){var s=i.data;if(s.isReply){var o=s.callbackId;if(s.callbackId in n){var u=n[o];delete n[o],"error"in s?u.reject(s.error):u.resolve(s.data)}else error("Cannot resolve callback "+o)}else if(s.action in r){var a=r[s.action];s.callbackId?Promise.resolve().then(function(){return a[0].call(a[1],s.data)}).then(function(e){t.postMessage({isReply:!0,callbackId:s.callbackId,data:e})},function(e){t.postMessage({isReply:!0,callbackId:s.callbackId,error:e})}):a[0].call(a[1],s.data)}else error("Unknown action from worker: "+s.action)}}function loadJpegStream(e,t,n){var r=new Image;r.onload=function(){n.resolve(e,r)},r.onerror=function(){n.resolve(e,null),warn("Error during JPEG image loading")},r.src=t}(function(e,t){typeof module=="object"&&typeof module.exports=="object"?module.exports=e.document?t(e,!0):function(e){if(!e.document)throw new Error("jQuery requires a window with a document");return t(e)}:t(e)})(typeof window!="undefined"?window:this,function(window,noGlobal){function isArraylike(e){var t=e.length,n=jQuery.type(e);return n==="function"||jQuery.isWindow(e)?!1:e.nodeType===1&&t?!0:n==="array"||t===0||typeof t=="number"&&t>0&&t-1 in e}function winnow(e,t,n){if(jQuery.isFunction(t))return jQuery.grep(e,function(e,r){return!!t.call(e,r,e)!==n});if(t.nodeType)return jQuery.grep(e,function(e){return e===t!==n});if(typeof t=="string"){if(risSimple.test(t))return jQuery.filter(t,e,n);t=jQuery.filter(t,e)}return jQuery.grep(e,function(e){return indexOf.call(t,e)>=0!==n})}function sibling(e,t){while((e=e[t])&&e.nodeType!==1);return e}function createOptions(e){var t=optionsCache[e]={};return jQuery.each(e.match(rnotwhite)||[],function(e,n){t[n]=!0}),t}function completed(){document.removeEventListener("DOMContentLoaded",completed,!1),window.removeEventListener("load",completed,!1),jQuery.ready()}function Data(){Object.defineProperty(this.cache={},0,{get:function(){return{}}}),this.expando=jQuery.expando+Data.uid++}function dataAttr(e,t,n){var r;if(n===undefined&&e.nodeType===1){r="data-"+t.replace(rmultiDash,"-$1").toLowerCase(),n=e.getAttribute(r);if(typeof n=="string"){try{n=n==="true"?!0:n==="false"?!1:n==="null"?null:+n+""===n?+n:rbrace.test(n)?jQuery.parseJSON(n):n}catch(i){}data_user.set(e,t,n)}else n=undefined}return n}function returnTrue(){return!0}function returnFalse(){return!1}function safeActiveElement(){try{return document.activeElement}catch(e){}}function manipulationTarget(e,t){return jQuery.nodeName(e,"table")&&jQuery.nodeName(t.nodeType!==11?t:t.firstChild,"tr")?e.getElementsByTagName("tbody")[0]||e.appendChild(e.ownerDocument.createElement("tbody")):e}function disableScript(e){return e.type=(e.getAttribute("type")!==null)+"/"+e.type,e}function restoreScript(e){var t=rscriptTypeMasked.exec(e.type);return t?e.type=t[1]:e.removeAttribute("type"),e}function setGlobalEval(e,t){var n=0,r=e.length;for(;n<r;n++)data_priv.set(e[n],"globalEval",!t||data_priv.get(t[n],"globalEval"))}function cloneCopyEvent(e,t){var n,r,i,s,o,u,a,f;if(t.nodeType!==1)return;if(data_priv.hasData(e)){s=data_priv.access(e),o=data_priv.set(t,s),f=s.events;if(f){delete o.handle,o.events={};for(i in f)for(n=0,r=f[i].length;n<r;n++)jQuery.event.add(t,i,f[i][n])}}data_user.hasData(e)&&(u=data_user.access(e),a=jQuery.extend({},u),data_user.set(t,a))}function getAll(e,t){var n=e.getElementsByTagName?e.getElementsByTagName(t||"*"):e.querySelectorAll?e.querySelectorAll(t||"*"):[];return t===undefined||t&&jQuery.nodeName(e,t)?jQuery.merge([e],n):n}function fixInput(e,t){var n=t.nodeName.toLowerCase();if(n==="input"&&rcheckableType.test(e.type))t.checked=e.checked;else if(n==="input"||n==="textarea")t.defaultValue=e.defaultValue}function actualDisplay(e,t){var n,r=jQuery(t.createElement(e)).appendTo(t.body),i=window.getDefaultComputedStyle&&(n=window.getDefaultComputedStyle(r[0]))?n.display:jQuery.css(r[0],"display");return r.detach(),i}function defaultDisplay(e){var t=document,n=elemdisplay[e];if(!n){n=actualDisplay(e,t);if(n==="none"||!n)iframe=(iframe||jQuery("<iframe frameborder='0' width='0' height='0'/>")).appendTo(t.documentElement),t=iframe[0].contentDocument,t.write(),t.close(),n=actualDisplay(e,t),iframe.detach();elemdisplay[e]=n}return n}function curCSS(e,t,n){var r,i,s,o,u=e.style;return n=n||getStyles(e),n&&(o=n.getPropertyValue(t)||n[t]),n&&(o===""&&!jQuery.contains(e.ownerDocument,e)&&(o=jQuery.style(e,t)),rnumnonpx.test(o)&&rmargin.test(t)&&(r=u.width,i=u.minWidth,s=u.maxWidth,u.minWidth=u.maxWidth=u.width=o,o=n.width,u.width=r,u.minWidth=i,u.maxWidth=s)),o!==undefined?o+"":o}function addGetHookIf(e,t){return{get:function(){if(e()){delete this.get;return}return(this.get=t).apply(this,arguments)}}}function vendorPropName(e,t){if(t in e)return t;var n=t[0].toUpperCase()+t.slice(1),r=t,i=cssPrefixes.length;while(i--){t=cssPrefixes[i]+n;if(t in e)return t}return r}function setPositiveNumber(e,t,n){var r=rnumsplit.exec(t);return r?Math.max(0,r[1]-(n||0))+(r[2]||"px"):t}function augmentWidthOrHeight(e,t,n,r,i){var s=n===(r?"border":"content")?4:t==="width"?1:0,o=0;for(;s<4;s+=2)n==="margin"&&(o+=jQuery.css(e,n+cssExpand[s],!0,i)),r?(n==="content"&&(o-=jQuery.css(e,"padding"+cssExpand[s],!0,i)),n!=="margin"&&(o-=jQuery.css(e,"border"+cssExpand[s]+"Width",!0,i))):(o+=jQuery.css(e,"padding"+cssExpand[s],!0,i),n!=="padding"&&(o+=jQuery.css(e,"border"+cssExpand[s]+"Width",!0,i)));return o}function getWidthOrHeight(e,t,n){var r=!0,i=t==="width"?e.offsetWidth:e.offsetHeight,s=getStyles(e),o=jQuery.css(e,"boxSizing",!1,s)==="border-box";if(i<=0||i==null){i=curCSS(e,t,s);if(i<0||i==null)i=e.style[t];if(rnumnonpx.test(i))return i;r=o&&(support.boxSizingReliable()||i===e.style[t]),i=parseFloat(i)||0}return i+augmentWidthOrHeight(e,t,n||(o?"border":"content"),r,s)+"px"}function showHide(e,t){var n,r,i,s=[],o=0,u=e.length;for(;o<u;o++){r=e[o];if(!r.style)continue;s[o]=data_priv.get(r,"olddisplay"),n=r.style.display,t?(!s[o]&&n==="none"&&(r.style.display=""),r.style.display===""&&isHidden(r)&&(s[o]=data_priv.access(r,"olddisplay",defaultDisplay(r.nodeName)))):(i=isHidden(r),(n!=="none"||!i)&&data_priv.set(r,"olddisplay",i?n:jQuery.css(r,"display")))}for(o=0;o<u;o++){r=e[o];if(!r.style)continue;if(!t||r.style.display==="none"||r.style.display==="")r.style.display=t?s[o]||"":"none"}return e}function Tween(e,t,n,r,i){return new Tween.prototype.init(e,t,n,r,i)}function createFxNow(){return setTimeout(function(){fxNow=undefined}),fxNow=jQuery.now()}function genFx(e,t){var n,r=0,i={height:e};t=t?1:0;for(;r<4;r+=2-t)n=cssExpand[r],i["margin"+n]=i["padding"+n]=e;return t&&(i.opacity=i.width=e),i}function createTween(e,t,n){var r,i=(tweeners[t]||[]).concat(tweeners["*"]),s=0,o=i.length;for(;s<o;s++)if(r=i[s].call(n,t,e))return r}function defaultPrefilter(e,t,n){var r,i,s,o,u,a,f,l,c=this,h={},p=e.style,d=e.nodeType&&isHidden(e),v=data_priv.get(e,"fxshow");n.queue||(u=jQuery._queueHooks(e,"fx"),u.unqueued==null&&(u.unqueued=0,a=u.empty.fire,u.empty.fire=function(){u.unqueued||a()}),u.unqueued++,c.always(function(){c.always(function(){u.unqueued--,jQuery.queue(e,"fx").length||u.empty.fire()})})),e.nodeType===1&&("height"in t||"width"in t)&&(n.overflow=[p.overflow,p.overflowX,p.overflowY],f=jQuery.css(e,"display"),l=f==="none"?data_priv.get(e,"olddisplay")||defaultDisplay(e.nodeName):f,l==="inline"&&jQuery.css(e,"float")==="none"&&(p.display="inline-block")),n.overflow&&(p.overflow="hidden",c.always(function(){p.overflow=n.overflow[0],p.overflowX=n.overflow[1],p.overflowY=n.overflow[2]}));for(r in t){i=t[r];if(rfxtypes.exec(i)){delete t[r],s=s||i==="toggle";if(i===(d?"hide":"show")){if(i!=="show"||!v||v[r]===undefined)continue;d=!0}h[r]=v&&v[r]||jQuery.style(e,r)}else f=undefined}if(!jQuery.isEmptyObject(h)){v?"hidden"in v&&(d=v.hidden):v=data_priv.access(e,"fxshow",{}),s&&(v.hidden=!d),d?jQuery(e).show():c.done(function(){jQuery(e).hide()}),c.done(function(){var t;data_priv.remove(e,"fxshow");for(t in h)jQuery.style(e,t,h[t])});for(r in h)o=createTween(d?v[r]:0,r,c),r in v||(v[r]=o.start,d&&(o.end=o.start,o.start=r==="width"||r==="height"?1:0))}else(f==="none"?defaultDisplay(e.nodeName):f)==="inline"&&(p.display=f)}function propFilter(e,t){var n,r,i,s,o;for(n in e){r=jQuery.camelCase(n),i=t[r],s=e[n],jQuery.isArray(s)&&(i=s[1],s=e[n]=s[0]),n!==r&&(e[r]=s,delete e[n]),o=jQuery.cssHooks[r];if(o&&"expand"in o){s=o.expand(s),delete e[r];for(n in s)n in e||(e[n]=s[n],t[n]=i)}else t[r]=i}}function Animation(e,t,n){var r,i,s=0,o=animationPrefilters.length,u=jQuery.Deferred().always(function(){delete a.elem}),a=function(){if(i)return!1;var t=fxNow||createFxNow(),n=Math.max(0,f.startTime+f.duration-t),r=n/f.duration||0,s=1-r,o=0,a=f.tweens.length;for(;o<a;o++)f.tweens[o].run(s);return u.notifyWith(e,[f,s,n]),s<1&&a?n:(u.resolveWith(e,[f]),!1)},f=u.promise({elem:e,props:jQuery.extend({},t),opts:jQuery.extend(!0,{specialEasing:{}},n),originalProperties:t,originalOptions:n,startTime:fxNow||createFxNow(),duration:n.duration,tweens:[],createTween:function(t,n){var r=jQuery.Tween(e,f.opts,t,n,f.opts.specialEasing[t]||f.opts.easing);return f.tweens.push(r),r},stop:function(t){var n=0,r=t?f.tweens.length:0;if(i)return this;i=!0;for(;n<r;n++)f.tweens[n].run(1);return t?u.resolveWith(e,[f,t]):u.rejectWith(e,[f,t]),this}}),l=f.props;propFilter(l,f.opts.specialEasing);for(;s<o;s++){r=animationPrefilters[s].call(f,e,l,f.opts);if(r)return r}return jQuery.map(l,createTween,f),jQuery.isFunction(f.opts.start)&&f.opts.start.call(e,f),jQuery.fx.timer(jQuery.extend(a,{elem:e,anim:f,queue:f.opts.queue})),f.progress(f.opts.progress).done(f.opts.done,f.opts.complete).fail(f.opts.fail).always(f.opts.always)}function addToPrefiltersOrTransports(e){return function(t,n){typeof t!="string"&&(n=t,t="*");var r,i=0,s=t.toLowerCase().match(rnotwhite)||[];if(jQuery.isFunction(n))while(r=s[i++])r[0]==="+"?(r=r.slice(1)||"*",(e[r]=e[r]||[]).unshift(n)):(e[r]=e[r]||[]).push(n)}}function inspectPrefiltersOrTransports(e,t,n,r){function o(u){var a;return i[u]=!0,jQuery.each(e[u]||[],function(e,u){var f=u(t,n,r);if(typeof f=="string"&&!s&&!i[f])return t.dataTypes.unshift(f),o(f),!1;if(s)return!(a=f)}),a}var i={},s=e===transports;return o(t.dataTypes[0])||!i["*"]&&o("*")}function ajaxExtend(e,t){var n,r,i=jQuery.ajaxSettings.flatOptions||{};for(n in t)t[n]!==undefined&&((i[n]?e:r||(r={}))[n]=t[n]);return r&&jQuery.extend(!0,e,r),e}function ajaxHandleResponses(e,t,n){var r,i,s,o,u=e.contents,a=e.dataTypes;while(a[0]==="*")a.shift(),r===undefined&&(r=e.mimeType||t.getResponseHeader("Content-Type"));if(r)for(i in u)if(u[i]&&u[i].test(r)){a.unshift(i);break}if(a[0]in n)s=a[0];else{for(i in n){if(!a[0]||e.converters[i+" "+a[0]]){s=i;break}o||(o=i)}s=s||o}if(s)return s!==a[0]&&a.unshift(s),n[s]}function ajaxConvert(e,t,n,r){var i,s,o,u,a,f={},l=e.dataTypes.slice();if(l[1])for(o in e.converters)f[o.toLowerCase()]=e.converters[o];s=l.shift();while(s){e.responseFields[s]&&(n[e.responseFields[s]]=t),!a&&r&&e.dataFilter&&(t=e.dataFilter(t,e.dataType)),a=s,s=l.shift();if(s)if(s==="*")s=a;else if(a!=="*"&&a!==s){o=f[a+" "+s]||f["* "+s];if(!o)for(i in f){u=i.split(" ");if(u[1]===s){o=f[a+" "+u[0]]||f["* "+u[0]];if(o){o===!0?o=f[i]:f[i]!==!0&&(s=u[0],l.unshift(u[1]));break}}}if(o!==!0)if(o&&e["throws"])t=o(t);else try{t=o(t)}catch(c){return{state:"parsererror",error:o?c:"No conversion from "+a+" to "+s}}}}return{state:"success",data:t}}function buildParams(e,t,n,r){var i;if(jQuery.isArray(t))jQuery.each(t,function(t,i){n||rbracket.test(e)?r(e,i):buildParams(e+"["+(typeof i=="object"?t:"")+"]",i,n,r)});else if(!n&&jQuery.type(t)==="object")for(i in t)buildParams(e+"["+i+"]",t[i],n,r);else r(e,t)}function getWindow(e){return jQuery.isWindow(e)?e:e.nodeType===9&&e.defaultView}var arr=[],slice=arr.slice,concat=arr.concat,push=arr.push,indexOf=arr.indexOf,class2type={},toString=class2type.toString,hasOwn=class2type.hasOwnProperty,support={},document=window.document,version="2.1.3",jQuery=function(e,t){return new jQuery.fn.init(e,t)},rtrim=/^[\s\uFEFF\xA0]+|[\s\uFEFF\xA0]+$/g,rmsPrefix=/^-ms-/,rdashAlpha=/-([\da-z])/gi,fcamelCase=function(e,t){return t.toUpperCase()};jQuery.fn=jQuery.prototype={jquery:version,constructor:jQuery,selector:"",length:0,toArray:function(){return slice.call(this)},get:function(e){return e!=null?e<0?this[e+this.length]:this[e]:slice.call(this)},pushStack:function(e){var t=jQuery.merge(this.constructor(),e);return t.prevObject=this,t.context=this.context,t},each:function(e,t){return jQuery.each(this,e,t)},map:function(e){return this.pushStack(jQuery.map(this,function(t,n){return e.call(t,n,t)}))},slice:function(){return this.pushStack(slice.apply(this,arguments))},first:function(){return this.eq(0)},last:function(){return this.eq(-1)},eq:function(e){var t=this.length,n=+e+(e<0?t:0);return this.pushStack(n>=0&&n<t?[this[n]]:[])},end:function(){return this.prevObject||this.constructor(null)},push:push,sort:arr.sort,splice:arr.splice},jQuery.extend=jQuery.fn.extend=function(){var e,t,n,r,i,s,o=arguments[0]||{},u=1,a=arguments.length,f=!1;typeof o=="boolean"&&(f=o,o=arguments[u]||{},u++),typeof o!="object"&&!jQuery.isFunction(o)&&(o={}),u===a&&(o=this,u--);for(;u<a;u++)if((e=arguments[u])!=null)for(t in e){n=o[t],r=e[t];if(o===r)continue;f&&r&&(jQuery.isPlainObject(r)||(i=jQuery.isArray(r)))?(i?(i=!1,s=n&&jQuery.isArray(n)?n:[]):s=n&&jQuery.isPlainObject(n)?n:{},o[t]=jQuery.extend(f,s,r)):r!==undefined&&(o[t]=r)}return o},jQuery.extend({expando:"jQuery"+(version+Math.random()).replace(/\D/g,""),isReady:!0,error:function(e){throw new Error(e)},noop:function(){},isFunction:function(e){return jQuery.type(e)==="function"},isArray:Array.isArray,isWindow:function(e){return e!=null&&e===e.window},isNumeric:function(e){return!jQuery.isArray(e)&&e-parseFloat(e)+1>=0},isPlainObject:function(e){return jQuery.type(e)!=="object"||e.nodeType||jQuery.isWindow(e)?!1:e.constructor&&!hasOwn.call(e.constructor.prototype,"isPrototypeOf")?!1:!0},isEmptyObject:function(e){var t;for(t in e)return!1;return!0},type:function(e){return e==null?e+"":typeof e=="object"||typeof e=="function"?class2type[toString.call(e)]||"object":typeof e},globalEval:function(code){var script,indirect=eval;code=jQuery.trim(code),code&&(code.indexOf("use strict")===1?(script=document.createElement("script"),script.text=code,document.head.appendChild(script).parentNode.removeChild(script)):indirect(code))},camelCase:function(e){return e.replace(rmsPrefix,"ms-").replace(rdashAlpha,fcamelCase)},nodeName:function(e,t){return e.nodeName&&e.nodeName.toLowerCase()===t.toLowerCase()},each:function(e,t,n){var r,i=0,s=e.length,o=isArraylike(e);if(n)if(o)for(;i<s;i++){r=t.apply(e[i],n);if(r===!1)break}else for(i in e){r=t.apply(e[i],n);if(r===!1)break}else if(o)for(;i<s;i++){r=t.call(e[i],i,e[i]);if(r===!1)break}else for(i in e){r=t.call(e[i],i,e[i]);if(r===!1)break}return e},trim:function(e){return e==null?"":(e+"").replace(rtrim,"")},makeArray:function(e,t){var n=t||[];return e!=null&&(isArraylike(Object(e))?jQuery.merge(n,typeof e=="string"?[e]:e):push.call(n,e)),n},inArray:function(e,t,n){return t==null?-1:indexOf.call(t,e,n)},merge:function(e,t){var n=+t.length,r=0,i=e.length;for(;r<n;r++)e[i++]=t[r];return e.length=i,e},grep:function(e,t,n){var r,i=[],s=0,o=e.length,u=!n;for(;s<o;s++)r=!t(e[s],s),r!==u&&i.push(e[s]);return i},map:function(e,t,n){var r,i=0,s=e.length,o=isArraylike(e),u=[];if(o)for(;i<s;i++)r=t(e[i],i,n),r!=null&&u.push(r);else for(i in e)r=t(e[i],i,n),r!=null&&u.push(r);return concat.apply([],u)},guid:1,proxy:function(e,t){var n,r,i;return typeof t=="string"&&(n=e[t],t=e,e=n),jQuery.isFunction(e)?(r=slice.call(arguments,2),i=function(){return e.apply(t||this,r.concat(slice.call(arguments)))},i.guid=e.guid=e.guid||jQuery.guid++,i):undefined},now:Date.now,support:support}),jQuery.each("Boolean Number String Function Array Date RegExp Object Error".split(" "),function(e,t){class2type["[object "+t+"]"]=t.toLowerCase()});var Sizzle=function(e){function ot(e,t,r,i){var s,u,f,l,c,d,g,y,S,x;(t?t.ownerDocument||t:E)!==p&&h(t),t=t||p,r=r||[],l=t.nodeType;if(typeof e!="string"||!e||l!==1&&l!==9&&l!==11)return r;if(!i&&v){if(l!==11&&(s=Z.exec(e)))if(f=s[1]){if(l===9){u=t.getElementById(f);if(!u||!u.parentNode)return r;if(u.id===f)return r.push(u),r}else if(t.ownerDocument&&(u=t.ownerDocument.getElementById(f))&&b(t,u)&&u.id===f)return r.push(u),r}else{if(s[2])return D.apply(r,t.getElementsByTagName(e)),r;if((f=s[3])&&n.getElementsByClassName)return D.apply(r,t.getElementsByClassName(f)),r}if(n.qsa&&(!m||!m.test(e))){y=g=w,S=t,x=l!==1&&e;if(l===1&&t.nodeName.toLowerCase()!=="object"){d=o(e),(g=t.getAttribute("id"))?y=g.replace(tt,"\\$&"):t.setAttribute("id",y),y="[id='"+y+"'] ",c=d.length;while(c--)d[c]=y+gt(d[c]);S=et.test(e)&&vt(t.parentNode)||t,x=d.join(",")}if(x)try{return D.apply(r,S.querySelectorAll(x)),r}catch(T){}finally{g||t.removeAttribute("id")}}}return a(e.replace(z,"$1"),t,r,i)}function ut(){function t(n,i){return e.push(n+" ")>r.cacheLength&&delete t[e.shift()],t[n+" "]=i}var e=[];return t}function at(e){return e[w]=!0,e}function ft(e){var t=p.createElement("div");try{return!!e(t)}catch(n){return!1}finally{t.parentNode&&t.parentNode.removeChild(t),t=null}}function lt(e,t){var n=e.split("|"),i=e.length;while(i--)r.attrHandle[n[i]]=t}function ct(e,t){var n=t&&e,r=n&&e.nodeType===1&&t.nodeType===1&&(~t.sourceIndex||L)-(~e.sourceIndex||L);if(r)return r;if(n)while(n=n.nextSibling)if(n===t)return-1;return e?1:-1}function ht(e){return function(t){var n=t.nodeName.toLowerCase();return n==="input"&&t.type===e}}function pt(e){return function(t){var n=t.nodeName.toLowerCase();return(n==="input"||n==="button")&&t.type===e}}function dt(e){return at(function(t){return t=+t,at(function(n,r){var i,s=e([],n.length,t),o=s.length;while(o--)n[i=s[o]]&&(n[i]=!(r[i]=n[i]))})})}function vt(e){return e&&typeof e.getElementsByTagName!="undefined"&&e}function mt(){}function gt(e){var t=0,n=e.length,r="";for(;t<n;t++)r+=e[t].value;return r}function yt(e,t,n){var r=t.dir,i=n&&r==="parentNode",s=x++;return t.first?function(t,n,s){while(t=t[r])if(t.nodeType===1||i)return e(t,n,s)}:function(t,n,o){var u,a,f=[S,s];if(o){while(t=t[r])if(t.nodeType===1||i)if(e(t,n,o))return!0}else while(t=t[r])if(t.nodeType===1||i){a=t[w]||(t[w]={});if((u=a[r])&&u[0]===S&&u[1]===s)return f[2]=u[2];a[r]=f;if(f[2]=e(t,n,o))return!0}}}function bt(e){return e.length>1?function(t,n,r){var i=e.length;while(i--)if(!e[i](t,n,r))return!1;return!0}:e[0]}function wt(e,t,n){var r=0,i=t.length;for(;r<i;r++)ot(e,t[r],n);return n}function Et(e,t,n,r,i){var s,o=[],u=0,a=e.length,f=t!=null;for(;u<a;u++)if(s=e[u])if(!n||n(s,r,i))o.push(s),f&&t.push(u);return o}function St(e,t,n,r,i,s){return r&&!r[w]&&(r=St(r)),i&&!i[w]&&(i=St(i,s)),at(function(s,o,u,a){var f,l,c,h=[],p=[],d=o.length,v=s||wt(t||"*",u.nodeType?[u]:u,[]),m=e&&(s||!t)?Et(v,h,e,u,a):v,g=n?i||(s?e:d||r)?[]:o:m;n&&n(m,g,u,a);if(r){f=Et(g,p),r(f,[],u,a),l=f.length;while(l--)if(c=f[l])g[p[l]]=!(m[p[l]]=c)}if(s){if(i||e){if(i){f=[],l=g.length;while(l--)(c=g[l])&&f.push(m[l]=c);i(null,g=[],f,a)}l=g.length;while(l--)(c=g[l])&&(f=i?H(s,c):h[l])>-1&&(s[f]=!(o[f]=c))}}else g=Et(g===o?g.splice(d,g.length):g),i?i(null,o,g,a):D.apply(o,g)})}function xt(e){var t,n,i,s=e.length,o=r.relative[e[0].type],u=o||r.relative[" "],a=o?1:0,l=yt(function(e){return e===t},u,!0),c=yt(function(e){return H(t,e)>-1},u,!0),h=[function(e,n,r){var i=!o&&(r||n!==f)||((t=n).nodeType?l(e,n,r):c(e,n,r));return t=null,i}];for(;a<s;a++)if(n=r.relative[e[a].type])h=[yt(bt(h),n)];else{n=r.filter[e[a].type].apply(null,e[a].matches);if(n[w]){i=++a;for(;i<s;i++)if(r.relative[e[i].type])break;return St(a>1&&bt(h),a>1&&gt(e.slice(0,a-1).concat({value:e[a-2].type===" "?"*":""})).replace(z,"$1"),n,a<i&&xt(e.slice(a,i)),i<s&&xt(e=e.slice(i)),i<s&&gt(e))}h.push(n)}return bt(h)}function Tt(e,t){var n=t.length>0,i=e.length>0,s=function(s,o,u,a,l){var c,h,d,v=0,m="0",g=s&&[],y=[],b=f,w=s||i&&r.find.TAG("*",l),E=S+=b==null?1:Math.random()||.1,x=w.length;l&&(f=o!==p&&o);for(;m!==x&&(c=w[m])!=null;m++){if(i&&c){h=0;while(d=e[h++])if(d(c,o,u)){a.push(c);break}l&&(S=E)}n&&((c=!d&&c)&&v--,s&&g.push(c))}v+=m;if(n&&m!==v){h=0;while(d=t[h++])d(g,y,o,u);if(s){if(v>0)while(m--)!g[m]&&!y[m]&&(y[m]=M.call(a));y=Et(y)}D.apply(a,y),l&&!s&&y.length>0&&v+t.length>1&&ot.uniqueSort(a)}return l&&(S=E,f=b),g};return n?at(s):s}var t,n,r,i,s,o,u,a,f,l,c,h,p,d,v,m,g,y,b,w="sizzle"+1*new Date,E=e.document,S=0,x=0,T=ut(),N=ut(),C=ut(),k=function(e,t){return e===t&&(c=!0),0},L=1<<31,A={}.hasOwnProperty,O=[],M=O.pop,_=O.push,D=O.push,P=O.slice,H=function(e,t){var n=0,r=e.length;for(;n<r;n++)if(e[n]===t)return n;return-1},B="checked|selected|async|autofocus|autoplay|controls|defer|disabled|hidden|ismap|loop|multiple|open|readonly|required|scoped",j="[\\x20\\t\\r\\n\\f]",F="(?:\\\\.|[\\w-]|[^\\x00-\\xa0])+",I=F.replace("w","w#"),q="\\["+j+"*("+F+")(?:"+j+"*([*^$|!~]?=)"+j+"*(?:'((?:\\\\.|[^\\\\'])*)'|\"((?:\\\\.|[^\\\\\"])*)\"|("+I+"))|)"+j+"*\\]",R=":("+F+")(?:\\(("+"('((?:\\\\.|[^\\\\'])*)'|\"((?:\\\\.|[^\\\\\"])*)\")|"+"((?:\\\\.|[^\\\\()[\\]]|"+q+")*)|"+".*"+")\\)|)",U=new RegExp(j+"+","g"),z=new RegExp("^"+j+"+|((?:^|[^\\\\])(?:\\\\.)*)"+j+"+$","g"),W=new RegExp("^"+j+"*,"+j+"*"),X=new RegExp("^"+j+"*([>+~]|"+j+")"+j+"*"),V=new RegExp("="+j+"*([^\\]'\"]*?)"+j+"*\\]","g"),$=new RegExp(R),J=new RegExp("^"+I+"$"),K={ID:new RegExp("^#("+F+")"),CLASS:new RegExp("^\\.("+F+")"),TAG:new RegExp("^("+F.replace("w","w*")+")"),ATTR:new RegExp("^"+q),PSEUDO:new RegExp("^"+R),CHILD:new RegExp("^:(only|first|last|nth|nth-last)-(child|of-type)(?:\\("+j+"*(even|odd|(([+-]|)(\\d*)n|)"+j+"*(?:([+-]|)"+j+"*(\\d+)|))"+j+"*\\)|)","i"),bool:new RegExp("^(?:"+B+")$","i"),needsContext:new RegExp("^"+j+"*[>+~]|:(even|odd|eq|gt|lt|nth|first|last)(?:\\("+j+"*((?:-\\d)?\\d*)"+j+"*\\)|)(?=[^-]|$)","i")},Q=/^(?:input|select|textarea|button)$/i,G=/^h\d$/i,Y=/^[^{]+\{\s*\[native \w/,Z=/^(?:#([\w-]+)|(\w+)|\.([\w-]+))$/,et=/[+~]/,tt=/'|\\/g,nt=new RegExp("\\\\([\\da-f]{1,6}"+j+"?|("+j+")|.)","ig"),rt=function(e,t,n){var r="0x"+t-65536;return r!==r||n?t:r<0?String.fromCharCode(r+65536):String.fromCharCode(r>>10|55296,r&1023|56320)},it=function(){h()};try{D.apply(O=P.call(E.childNodes),E.childNodes),O[E.childNodes.length].nodeType}catch(st){D={apply:O.length?function(e,t){_.apply(e,P.call(t))}:function(e,t){var n=e.length,r=0;while(e[n++]=t[r++]);e.length=n-1}}}n=ot.support={},s=ot.isXML=function(e){var t=e&&(e.ownerDocument||e).documentElement;return t?t.nodeName!=="HTML":!1},h=ot.setDocument=function(e){var t,i,o=e?e.ownerDocument||e:E;if(o===p||o.nodeType!==9||!o.documentElement)return p;p=o,d=o.documentElement,i=o.defaultView,i&&i!==i.top&&(i.addEventListener?i.addEventListener("unload",it,!1):i.attachEvent&&i.attachEvent("onunload",it)),v=!s(o),n.attributes=ft(function(e){return e.className="i",!e.getAttribute("className")}),n.getElementsByTagName=ft(function(e){return e.appendChild(o.createComment("")),!e.getElementsByTagName("*").length}),n.getElementsByClassName=Y.test(o.getElementsByClassName),n.getById=ft(function(e){return d.appendChild(e).id=w,!o.getElementsByName||!o.getElementsByName(w).length}),n.getById?(r.find.ID=function(e,t){if(typeof t.getElementById!="undefined"&&v){var n=t.getElementById(e);return n&&n.parentNode?[n]:[]}},r.filter.ID=function(e){var t=e.replace(nt,rt);return function(e){return e.getAttribute("id")===t}}):(delete r.find.ID,r.filter.ID=function(e){var t=e.replace(nt,rt);return function(e){var n=typeof e.getAttributeNode!="undefined"&&e.getAttributeNode("id");return n&&n.value===t}}),r.find.TAG=n.getElementsByTagName?function(e,t){if(typeof t.getElementsByTagName!="undefined")return t.getElementsByTagName(e);if(n.qsa)return t.querySelectorAll(e)}:function(e,t){var n,r=[],i=0,s=t.getElementsByTagName(e);if(e==="*"){while(n=s[i++])n.nodeType===1&&r.push(n);return r}return s},r.find.CLASS=n.getElementsByClassName&&function(e,t){if(v)return t.getElementsByClassName(e)},g=[],m=[];if(n.qsa=Y.test(o.querySelectorAll))ft(function(e){d.appendChild(e).innerHTML="<a id='"+w+"'></a>"+"<select id='"+w+"-\f]' msallowcapture=''>"+"<option selected=''></option></select>",e.querySelectorAll("[msallowcapture^='']").length&&m.push("[*^$]="+j+"*(?:''|\"\")"),e.querySelectorAll("[selected]").length||m.push("\\["+j+"*(?:value|"+B+")"),e.querySelectorAll("[id~="+w+"-]").length||m.push("~="),e.querySelectorAll(":checked").length||m.push(":checked"),e.querySelectorAll("a#"+w+"+*").length||m.push(".#.+[+~]")}),ft(function(e){var t=o.createElement("input");t.setAttribute("type","hidden"),e.appendChild(t).setAttribute("name","D"),e.querySelectorAll("[name=d]").length&&m.push("name"+j+"*[*^$|!~]?="),e.querySelectorAll(":enabled").length||m.push(":enabled",":disabled"),e.querySelectorAll("*,:x"),m.push(",.*:")});return(n.matchesSelector=Y.test(y=d.matches||d.webkitMatchesSelector||d.mozMatchesSelector||d.oMatchesSelector||d.msMatchesSelector))&&ft(function(e){n.disconnectedMatch=y.call(e,"div"),y.call(e,"[s!='']:x"),g.push("!=",R)}),m=m.length&&new RegExp(m.join("|")),g=g.length&&new RegExp(g.join("|")),t=Y.test(d.compareDocumentPosition),b=t||Y.test(d.contains)?function(e,t){var n=e.nodeType===9?e.documentElement:e,r=t&&t.parentNode;return e===r||!!r&&r.nodeType===1&&!!(n.contains?n.contains(r):e.compareDocumentPosition&&e.compareDocumentPosition(r)&16)}:function(e,t){if(t)while(t=t.parentNode)if(t===e)return!0;return!1},k=t?function(e,t){if(e===t)return c=!0,0;var r=!e.compareDocumentPosition-!t.compareDocumentPosition;return r?r:(r=(e.ownerDocument||e)===(t.ownerDocument||t)?e.compareDocumentPosition(t):1,r&1||!n.sortDetached&&t.compareDocumentPosition(e)===r?e===o||e.ownerDocument===E&&b(E,e)?-1:t===o||t.ownerDocument===E&&b(E,t)?1:l?H(l,e)-H(l,t):0:r&4?-1:1)}:function(e,t){if(e===t)return c=!0,0;var n,r=0,i=e.parentNode,s=t.parentNode,u=[e],a=[t];if(!i||!s)return e===o?-1:t===o?1:i?-1:s?1:l?H(l,e)-H(l,t):0;if(i===s)return ct(e,t);n=e;while(n=n.parentNode)u.unshift(n);n=t;while(n=n.parentNode)a.unshift(n);while(u[r]===a[r])r++;return r?ct(u[r],a[r]):u[r]===E?-1:a[r]===E?1:0},o},ot.matches=function(e,t){return ot(e,null,null,t)},ot.matchesSelector=function(e,t){(e.ownerDocument||e)!==p&&h(e),t=t.replace(V,"='$1']");if(n.matchesSelector&&v&&(!g||!g.test(t))&&(!m||!m.test(t)))try{var r=y.call(e,t);if(r||n.disconnectedMatch||e.document&&e.document.nodeType!==11)return r}catch(i){}return ot(t,p,null,[e]).length>0},ot.contains=function(e,t){return(e.ownerDocument||e)!==p&&h(e),b(e,t)},ot.attr=function(e,t){(e.ownerDocument||e)!==p&&h(e);var i=r.attrHandle[t.toLowerCase()],s=i&&A.call(r.attrHandle,t.toLowerCase())?i(e,t,!v):undefined;return s!==undefined?s:n.attributes||!v?e.getAttribute(t):(s=e.getAttributeNode(t))&&s.specified?s.value:null},ot.error=function(e){throw new Error("Syntax error, unrecognized expression: "+e)},ot.uniqueSort=function(e){var t,r=[],i=0,s=0;c=!n.detectDuplicates,l=!n.sortStable&&e.slice(0),e.sort(k);if(c){while(t=e[s++])t===e[s]&&(i=r.push(s));while(i--)e.splice(r[i],1)}return l=null,e},i=ot.getText=function(e){var t,n="",r=0,s=e.nodeType;if(!s)while(t=e[r++])n+=i(t);else if(s===1||s===9||s===11){if(typeof e.textContent=="string")return e.textContent;for(e=e.firstChild;e;e=e.nextSibling)n+=i(e)}else if(s===3||s===4)return e.nodeValue;return n},r=ot.selectors={cacheLength:50,createPseudo:at,match:K,attrHandle:{},find:{},relative:{">":{dir:"parentNode",first:!0}," ":{dir:"parentNode"},"+":{dir:"previousSibling",first:!0},"~":{dir:"previousSibling"}},preFilter:{ATTR:function(e){return e[1]=e[1].replace(nt,rt),e[3]=(e[3]||e[4]||e[5]||"").replace(nt,rt),e[2]==="~="&&(e[3]=" "+e[3]+" "),e.slice(0,4)},CHILD:function(e){return e[1]=e[1].toLowerCase(),e[1].slice(0,3)==="nth"?(e[3]||ot.error(e[0]),e[4]=+(e[4]?e[5]+(e[6]||1):2*(e[3]==="even"||e[3]==="odd")),e[5]=+(e[7]+e[8]||e[3]==="odd")):e[3]&&ot.error(e[0]),e},PSEUDO:function(e){var t,n=!e[6]&&e[2];return K.CHILD.test(e[0])?null:(e[3]?e[2]=e[4]||e[5]||"":n&&$.test(n)&&(t=o(n,!0))&&(t=n.indexOf(")",n.length-t)-n.length)&&(e[0]=e[0].slice(0,t),e[2]=n.slice(0,t)),e.slice(0,3))}},filter:{TAG:function(e){var t=e.replace(nt,rt).toLowerCase();return e==="*"?function(){return!0}:function(e){return e.nodeName&&e.nodeName.toLowerCase()===t}},CLASS:function(e){var t=T[e+" "];return t||(t=new RegExp("(^|"+j+")"+e+"("+j+"|$)"))&&T(e,function(e){return t.test(typeof e.className=="string"&&e.className||typeof e.getAttribute!="undefined"&&e.getAttribute("class")||"")})},ATTR:function(e,t,n){return function(r){var i=ot.attr(r,e);return i==null?t==="!=":t?(i+="",t==="="?i===n:t==="!="?i!==n:t==="^="?n&&i.indexOf(n)===0:t==="*="?n&&i.indexOf(n)>-1:t==="$="?n&&i.slice(-n.length)===n:t==="~="?(" "+i.replace(U," ")+" ").indexOf(n)>-1:t==="|="?i===n||i.slice(0,n.length+1)===n+"-":!1):!0}},CHILD:function(e,t,n,r,i){var s=e.slice(0,3)!=="nth",o=e.slice(-4)!=="last",u=t==="of-type";return r===1&&i===0?function(e){return!!e.parentNode}:function(t,n,a){var f,l,c,h,p,d,v=s!==o?"nextSibling":"previousSibling",m=t.parentNode,g=u&&t.nodeName.toLowerCase(),y=!a&&!u;if(m){if(s){while(v){c=t;while(c=c[v])if(u?c.nodeName.toLowerCase()===g:c.nodeType===1)return!1;d=v=e==="only"&&!d&&"nextSibling"}return!0}d=[o?m.firstChild:m.lastChild];if(o&&y){l=m[w]||(m[w]={}),f=l[e]||[],p=f[0]===S&&f[1],h=f[0]===S&&f[2],c=p&&m.childNodes[p];while(c=++p&&c&&c[v]||(h=p=0)||d.pop())if(c.nodeType===1&&++h&&c===t){l[e]=[S,p,h];break}}else if(y&&(f=(t[w]||(t[w]={}))[e])&&f[0]===S)h=f[1];else while(c=++p&&c&&c[v]||(h=p=0)||d.pop())if((u?c.nodeName.toLowerCase()===g:c.nodeType===1)&&++h){y&&((c[w]||(c[w]={}))[e]=[S,h]);if(c===t)break}return h-=i,h===r||h%r===0&&h/r>=0}}},PSEUDO:function(e,t){var n,i=r.pseudos[e]||r.setFilters[e.toLowerCase()]||ot.error("unsupported pseudo: "+e);return i[w]?i(t):i.length>1?(n=[e,e,"",t],r.setFilters.hasOwnProperty(e.toLowerCase())?at(function(e,n){var r,s=i(e,t),o=s.length;while(o--)r=H(e,s[o]),e[r]=!(n[r]=s[o])}):function(e){return i(e,0,n)}):i}},pseudos:{not:at(function(e){var t=[],n=[],r=u(e.replace(z,"$1"));return r[w]?at(function(e,t,n,i){var s,o=r(e,null,i,[]),u=e.length;while(u--)if(s=o[u])e[u]=!(t[u]=s)}):function(e,i,s){return t[0]=e,r(t,null,s,n),t[0]=null,!n.pop()}}),has:at(function(e){return function(t){return ot(e,t).length>0}}),contains:at(function(e){return e=e.replace(nt,rt),function(t){return(t.textContent||t.innerText||i(t)).indexOf(e)>-1}}),lang:at(function(e){return J.test(e||"")||ot.error("unsupported lang: "+e),e=e.replace(nt,rt).toLowerCase(),function(t){var n;do if(n=v?t.lang:t.getAttribute("xml:lang")||t.getAttribute("lang"))return n=n.toLowerCase(),n===e||n.indexOf(e+"-")===0;while((t=t.parentNode)&&t.nodeType===1);return!1}}),target:function(t){var n=e.location&&e.location.hash;return n&&n.slice(1)===t.id},root:function(e){return e===d},focus:function(e){return e===p.activeElement&&(!p.hasFocus||p.hasFocus())&&!!(e.type||e.href||~e.tabIndex)},enabled:function(e){return e.disabled===!1},disabled:function(e){return e.disabled===!0},checked:function(e){var t=e.nodeName.toLowerCase();return t==="input"&&!!e.checked||t==="option"&&!!e.selected},selected:function(e){return e.parentNode&&e.parentNode.selectedIndex,e.selected===!0},empty:function(e){for(e=e.firstChild;e;e=e.nextSibling)if(e.nodeType<6)return!1;return!0},parent:function(e){return!r.pseudos.empty(e)},header:function(e){return G.test(e.nodeName)},input:function(e){return Q.test(e.nodeName)},button:function(e){var t=e.nodeName.toLowerCase();return t==="input"&&e.type==="button"||t==="button"},text:function(e){var t;return e.nodeName.toLowerCase()==="input"&&e.type==="text"&&((t=e.getAttribute("type"))==null||t.toLowerCase()==="text")},first:dt(function(){return[0]}),last:dt(function(e,t){return[t-1]}),eq:dt(function(e,t,n){return[n<0?n+t:n]}),even:dt(function(e,t){var n=0;for(;n<t;n+=2)e.push(n);return e}),odd:dt(function(e,t){var n=1;for(;n<t;n+=2)e.push(n);return e}),lt:dt(function(e,t,n){var r=n<0?n+t:n;for(;--r>=0;)e.push(r);return e}),gt:dt(function(e,t,n){var r=n<0?n+t:n;for(;++r<t;)e.push(r);return e})}},r.pseudos.nth=r.pseudos.eq;for(t in{radio:!0,checkbox:!0,file:!0,password:!0,image:!0})r.pseudos[t]=ht(t);for(t in{submit:!0,reset:!0})r.pseudos[t]=pt(t);return mt.prototype=r.filters=r.pseudos,r.setFilters=new mt,o=ot.tokenize=function(e,t){var n,i,s,o,u,a,f,l=N[e+" "];if(l)return t?0:l.slice(0);u=e,a=[],f=r.preFilter;while(u){if(!n||(i=W.exec(u)))i&&(u=u.slice(i[0].length)||u),a.push(s=[]);n=!1;if(i=X.exec(u))n=i.shift(),s.push({value:n,type:i[0].replace(z," ")}),u=u.slice(n.length);for(o in r.filter)(i=K[o].exec(u))&&(!f[o]||(i=f[o](i)))&&(n=i.shift(),s.push({value:n,type:o,matches:i}),u=u.slice(n.length));if(!n)break}return t?u.length:u?ot.error(e):N(e,a).slice(0)},u=ot.compile=function(e,t){var n,r=[],i=[],s=C[e+" "];if(!s){t||(t=o(e)),n=t.length;while(n--)s=xt(t[n]),s[w]?r.push(s):i.push(s);s=C(e,Tt(i,r)),s.selector=e}return s},a=ot.select=function(e,t,i,s){var a,f,l,c,h,p=typeof e=="function"&&e,d=!s&&o(e=p.selector||e);i=i||[];if(d.length===1){f=d[0]=d[0].slice(0);if(f.length>2&&(l=f[0]).type==="ID"&&n.getById&&t.nodeType===9&&v&&r.relative[f[1].type]){t=(r.find.ID(l.matches[0].replace(nt,rt),t)||[])[0];if(!t)return i;p&&(t=t.parentNode),e=e.slice(f.shift().value.length)}a=K.needsContext.test(e)?0:f.length;while(a--){l=f[a];if(r.relative[c=l.type])break;if(h=r.find[c])if(s=h(l.matches[0].replace(nt,rt),et.test(f[0].type)&&vt(t.parentNode)||t)){f.splice(a,1),e=s.length&&gt(f);if(!e)return D.apply(i,s),i;break}}}return(p||u(e,d))(s,t,!v,i,et.test(e)&&vt(t.parentNode)||t),i},n.sortStable=w.split("").sort(k).join("")===w,n.detectDuplicates=!!c,h(),n.sortDetached=ft(function(e){return e.compareDocumentPosition(p.createElement("div"))&1}),ft(function(e){return e.innerHTML="<a href='#'></a>",e.firstChild.getAttribute("href")==="#"})||lt("type|href|height|width",function(e,t,n){if(!n)return e.getAttribute(t,t.toLowerCase()==="type"?1:2)}),(!n.attributes||!ft(function(e){return e.innerHTML="<input/>",e.firstChild.setAttribute("value",""),e.firstChild.getAttribute("value")===""}))&&lt("value",function(e,t,n){if(!n&&e.nodeName.toLowerCase()==="input")return e.defaultValue}),ft(function(e){return e.getAttribute("disabled")==null})||lt(B,function(e,t,n){var r;if(!n)return e[t]===!0?t.toLowerCase():(r=e.getAttributeNode(t))&&r.specified?r.value:null}),ot}(window);jQuery.find=Sizzle,jQuery.expr=Sizzle.selectors,jQuery.expr[":"]=jQuery.expr.pseudos,jQuery.unique=Sizzle.uniqueSort,jQuery.text=Sizzle.getText,jQuery.isXMLDoc=Sizzle.isXML,jQuery.contains=Sizzle.contains;var rneedsContext=jQuery.expr.match.needsContext,rsingleTag=/^<(\w+)\s*\/?>(?:<\/\1>|)$/,risSimple=/^.[^:#\[\.,]*$/;jQuery.filter=function(e,t,n){var r=t[0];return n&&(e=":not("+e+")"),t.length===1&&r.nodeType===1?jQuery.find.matchesSelector(r,e)?[r]:[]:jQuery.find.matches(e,jQuery.grep(t,function(e){return e.nodeType===1}))},jQuery.fn.extend({find:function(e){var t,n=this.length,r=[],i=this;if(typeof e!="string")return this.pushStack(jQuery(e).filter(function(){for(t=0;t<n;t++)if(jQuery.contains(i[t],this))return!0}));for(t=0;t<n;t++)jQuery.find(e,i[t],r);return r=this.pushStack(n>1?jQuery.unique(r):r),r.selector=this.selector?this.selector+" "+e:e,r},filter:function(e){return this.pushStack(winnow(this,e||[],!1))},not:function(e){return this.pushStack(winnow(this,e||[],!0))},is:function(e){return!!winnow(this,typeof e=="string"&&rneedsContext.test(e)?jQuery(e):e||[],!1).length}});var rootjQuery,rquickExpr=/^(?:\s*(<[\w\W]+>)[^>]*|#([\w-]*))$/,init=jQuery.fn.init=function(e,t){var n,r;if(!e)return this;if(typeof e=="string"){e[0]==="<"&&e[e.length-1]===">"&&e.length>=3?n=[null,e,null]:n=rquickExpr.exec(e);if(n&&(n[1]||!t)){if(n[1]){t=t instanceof jQuery?t[0]:t,jQuery.merge(this,jQuery.parseHTML(n[1],t&&t.nodeType?t.ownerDocument||t:document,!0));if(rsingleTag.test(n[1])&&jQuery.isPlainObject(t))for(n in t)jQuery.isFunction(this[n])?this[n](t[n]):this.attr(n,t[n]);return this}return r=document.getElementById(n[2]),r&&r.parentNode&&(this.length=1,this[0]=r),this.context=document,this.selector=e,this}return!t||t.jquery?(t||rootjQuery).find(e):this.constructor(t).find(e)}return e.nodeType?(this.context=this[0]=e,this.length=1,this):jQuery.isFunction(e)?typeof rootjQuery.ready!="undefined"?rootjQuery.ready(e):e(jQuery):(e.selector!==undefined&&(this.selector=e.selector,this.context=e.context),jQuery.makeArray(e,this))};init.prototype=jQuery.fn,rootjQuery=jQuery(document);var rparentsprev=/^(?:parents|prev(?:Until|All))/,guaranteedUnique={children:!0,contents:!0,next:!0,prev:!0};jQuery.extend({dir:function(e,t,n){var r=[],i=n!==undefined;while((e=e[t])&&e.nodeType!==9)if(e.nodeType===1){if(i&&jQuery(e).is(n))break;r.push(e)}return r},sibling:function(e,t){var n=[];for(;e;e=e.nextSibling)e.nodeType===1&&e!==t&&n.push(e);return n}}),jQuery.fn.extend({has:function(e){var t=jQuery(e,this),n=t.length;return this.filter(function(){var e=0;for(;e<n;e++)if(jQuery.contains(this,t[e]))return!0})},closest:function(e,t){var n,r=0,i=this.length,s=[],o=rneedsContext.test(e)||typeof e!="string"?jQuery(e,t||this.context):0;for(;r<i;r++)for(n=this[r];n&&n!==t;n=n.parentNode)if(n.nodeType<11&&(o?o.index(n)>-1:n.nodeType===1&&jQuery.find.matchesSelector(n,e))){s.push(n);break}return this.pushStack(s.length>1?jQuery.unique(s):s)},index:function(e){return e?typeof e=="string"?indexOf.call(jQuery(e),this[0]):indexOf.call(this,e.jquery?e[0]:e):this[0]&&this[0].parentNode?this.first().prevAll().length:-1},add:function(e,t){return this.pushStack(jQuery.unique(jQuery.merge(this.get(),jQuery(e,t))))},addBack:function(e){return this.add(e==null?this.prevObject:this.prevObject.filter(e))}}),jQuery.each({parent:function(e){var t=e.parentNode;return t&&t.nodeType!==11?t:null},parents:function(e){return jQuery.dir(e,"parentNode")},parentsUntil:function(e,t,n){return jQuery.dir(e,"parentNode",n)},next:function(e){return sibling(e,"nextSibling")},prev:function(e){return sibling(e,"previousSibling")},nextAll:function(e){return jQuery.dir(e,"nextSibling")},prevAll:function(e){return jQuery.dir(e,"previousSibling")},nextUntil:function(e,t,n){return jQuery.dir(e,"nextSibling",n)},prevUntil:function(e,t,n){return jQuery.dir(e,"previousSibling",n)},siblings:function(e){return jQuery.sibling((e.parentNode||{}).firstChild,e)},children:function(e){return jQuery.sibling(e.firstChild)},contents:function(e){return e.contentDocument||jQuery.merge([],e.childNodes)}},function(e,t){jQuery.fn[e]=function(n,r){var i=jQuery.map(this,t,n);return e.slice(-5)!=="Until"&&(r=n),r&&typeof r=="string"&&(i=jQuery.filter(r,i)),this.length>1&&(guaranteedUnique[e]||jQuery.unique(i),rparentsprev.test(e)&&i.reverse()),this.pushStack(i)}});var rnotwhite=/\S+/g,optionsCache={};jQuery.Callbacks=function(e){e=typeof e=="string"?optionsCache[e]||createOptions(e):jQuery.extend({},e);var t,n,r,i,s,o,u=[],a=!e.once&&[],f=function(c){t=e.memory&&c,n=!0,o=i||0,i=0,s=u.length,r=!0;for(;u&&o<s;o++)if(u[o].apply(c[0],c[1])===!1&&e.stopOnFalse){t=!1;break}r=!1,u&&(a?a.length&&f(a.shift()):t?u=[]:l.disable())},l={add:function(){if(u){var n=u.length;(function o(t){jQuery.each(t,function(t,n){var r=jQuery.type(n);r==="function"?(!e.unique||!l.has(n))&&u.push(n):n&&n.length&&r!=="string"&&o(n)})})(arguments),r?s=u.length:t&&(i=n,f(t))}return this},remove:function(){return u&&jQuery.each(arguments,function(e,t){var n;while((n=jQuery.inArray(t,u,n))>-1)u.splice(n,1),r&&(n<=s&&s--,n<=o&&o--)}),this},has:function(e){return e?jQuery.inArray(e,u)>-1:!!u&&!!u.length},empty:function(){return u=[],s=0,this},disable:function(){return u=a=t=undefined,this},disabled:function(){return!u},lock:function(){return a=undefined,t||l.disable(),this},locked:function(){return!a},fireWith:function(e,t){return u&&(!n||a)&&(t=t||[],t=[e,t.slice?t.slice():t],r?a.push(t):f(t)),this},fire:function(){return l.fireWith(this,arguments),this},fired:function(){return!!n}};return l},jQuery.extend({Deferred:function(e){var t=[["resolve","done",jQuery.Callbacks("once memory"),"resolved"],["reject","fail",jQuery.Callbacks("once memory"),"rejected"],["notify","progress",jQuery.Callbacks("memory")]],n="pending",r={state:function(){return n},always:function(){return i.done(arguments).fail(arguments),this},then:function(){var e=arguments;return jQuery.Deferred(function(n){jQuery.each(t,function(t,s){var o=jQuery.isFunction(e[t])&&e[t];i[s[1]](function(){var e=o&&o.apply(this,arguments);e&&jQuery.isFunction(e.promise)?e.promise().done(n.resolve).fail(n.reject).progress(n.notify):n[s[0]+"With"](this===r?n.promise():this,o?[e]:arguments)})}),e=null}).promise()},promise:function(e){return e!=null?jQuery.extend(e,r):r}},i={};return r.pipe=r.then,jQuery.each(t,function(e,s){var o=s[2],u=s[3];r[s[1]]=o.add,u&&o.add(function(){n=u},t[e^1][2].disable,t[2][2].lock),i[s[0]]=function(){return i[s[0]+"With"](this===i?r:this,arguments),this},i[s[0]+"With"]=o.fireWith}),r.promise(i),e&&e.call(i,i),i},when:function(e){var t=0,n=slice.call(arguments),r=n.length,i=r!==1||e&&jQuery.isFunction(e.promise)?r:0,s=i===1?e:jQuery.Deferred(),o=function(e,t,n){return function(r){t[e]=this,n[e]=arguments.length>1?slice.call(arguments):r,n===u?s.notifyWith(t,n):--i||s.resolveWith(t,n)}},u,a,f;if(r>1){u=new Array(r),a=new Array(r),f=new Array(r);for(;t<r;t++)n[t]&&jQuery.isFunction(n[t].promise)?n[t].promise().done(o(t,f,n)).fail(s.reject).progress(o(t,a,u)):--i}return i||s.resolveWith(f,n),s.promise()}});var readyList;jQuery.fn.ready=function(e){return jQuery.ready.promise().done(e),this},jQuery.extend({isReady:!1,readyWait:1,holdReady:function(e){e?jQuery.readyWait++:jQuery.ready(!0)},ready:function(e){if(e===!0?--jQuery.readyWait:jQuery.isReady)return;jQuery.isReady=!0;if(e!==!0&&--jQuery.readyWait>0)return;readyList.resolveWith(document,[jQuery]),jQuery.fn.triggerHandler&&(jQuery(document).triggerHandler("ready"),jQuery(document).off("ready"))}}),jQuery.ready.promise=function(e){return readyList||(readyList=jQuery.Deferred(),document.readyState==="complete"?setTimeout(jQuery.ready):(document.addEventListener("DOMContentLoaded",completed,!1),window.addEventListener("load",completed,!1))),readyList.promise(e)},jQuery.ready.promise();var access=jQuery.access=function(e,t,n,r,i,s,o){var u=0,a=e.length,f=n==null;if(jQuery.type(n)==="object"){i=!0;for(u in n)jQuery.access(e,t,u,n[u],!0,s,o)}else if(r!==undefined){i=!0,jQuery.isFunction(r)||(o=!0),f&&(o?(t.call(e,r),t=null):(f=t,t=function(e,t,n){return f.call(jQuery(e),n)}));if(t)for(;u<a;u++)t(e[u],n,o?r:r.call(e[u],u,t(e[u],n)))}return i?e:f?t.call(e):a?t(e[0],n):s};jQuery.acceptData=function(e){return e.nodeType===1||e.nodeType===9||!+e.nodeType},Data.uid=1,Data.accepts=jQuery.acceptData,Data.prototype={key:function(e){if(!Data.accepts(e))return 0;var t={},n=e[this.expando];if(!n){n=Data.uid++;try{t[this.expando]={value:n},Object.defineProperties(e,t)}catch(r){t[this.expando]=n,jQuery.extend(e,t)}}return this.cache[n]||(this.cache[n]={}),n},set:function(e,t,n){var r,i=this.key(e),s=this.cache[i];if(typeof t=="string")s[t]=n;else if(jQuery.isEmptyObject(s))jQuery.extend(this.cache[i],t);else for(r in t)s[r]=t[r];return s},get:function(e,t){var n=this.cache[this.key(e)];return t===undefined?n:n[t]},access:function(e,t,n){var r;return t===undefined||t&&typeof t=="string"&&n===undefined?(r=this.get(e,t),r!==undefined?r:this.get(e,jQuery.camelCase(t))):(this.set(e,t,n),n!==undefined?n:t)},remove:function(e,t){var n,r,i,s=this.key(e),o=this.cache[s];if(t===undefined)this.cache[s]={};else{jQuery.isArray(t)?r=t.concat(t.map(jQuery.camelCase)):(i=jQuery.camelCase(t),t in o?r=[t,i]:(r=i,r=r in o?[r]:r.match(rnotwhite)||[])),n=r.length;while(n--)delete o[r[n]]}},hasData:function(e){return!jQuery.isEmptyObject(this.cache[e[this.expando]]||{})},discard:function(e){e[this.expando]&&delete this.cache[e[this.expando]]}};var data_priv=new Data,data_user=new Data,rbrace=/^(?:\{[\w\W]*\}|\[[\w\W]*\])$/,rmultiDash=/([A-Z])/g;jQuery.extend({hasData:function(e){return data_user.hasData(e)||data_priv.hasData(e)},data:function(e,t,n){return data_user.access(e,t,n)},removeData:function(e,t){data_user.remove(e,t)},_data:function(e,t,n){return data_priv.access(e,t,n)},_removeData:function(e,t){data_priv.remove(e,t)}}),jQuery.fn.extend({data:function(e,t){var n,r,i,s=this[0],o=s&&s.attributes;if(e===undefined){if(this.length){i=data_user.get(s);if(s.nodeType===1&&!data_priv.get(s,"hasDataAttrs")){n=o.length;while(n--)o[n]&&(r=o[n].name,r.indexOf("data-")===0&&(r=jQuery.camelCase(r.slice(5)),dataAttr(s,r,i[r])));data_priv.set(s,"hasDataAttrs",!0)}}return i}return typeof e=="object"?this.each(function(){data_user.set(this,e)}):access(this,function(t){var n,r=jQuery.camelCase(e);if(s&&t===undefined){n=data_user.get(s,e);if(n!==undefined)return n;n=data_user.get(s,r);if(n!==undefined)return n;n=dataAttr(s,r,undefined);if(n!==undefined)return n;return}this.each(function(){var n=data_user.get(this,r);data_user.set(this,r,t),e.indexOf("-")!==-1&&n!==undefined&&data_user.set(this,e,t)})},null,t,arguments.length>1,null,!0)},removeData:function(e){return this.each(function(){data_user.remove(this,e)})}}),jQuery.extend({queue:function(e,t,n){var r;if(e)return t=(t||"fx")+"queue",r=data_priv.get(e,t),n&&(!r||jQuery.isArray(n)?r=data_priv.access(e,t,jQuery.makeArray(n)):r.push(n)),r||[]},dequeue:function(e,t){t=t||"fx";var n=jQuery.queue(e,t),r=n.length,i=n.shift(),s=jQuery._queueHooks(e,t),o=function(){jQuery.dequeue(e,t)};i==="inprogress"&&(i=n.shift(),r--),i&&(t==="fx"&&n.unshift("inprogress"),delete s.stop,i.call(e,o,s)),!r&&s&&s.empty.fire()},_queueHooks:function(e,t){var n=t+"queueHooks";return data_priv.get(e,n)||data_priv.access(e,n,{empty:jQuery.Callbacks("once memory").add(function(){data_priv.remove(e,[t+"queue",n])})})}}),jQuery.fn.extend({queue:function(e,t){var n=2;return typeof e!="string"&&(t=e,e="fx",n--),arguments.length<n?jQuery.queue(this[0],e):t===undefined?this:this.each(function(){var n=jQuery.queue(this,e,t);jQuery._queueHooks(this,e),e==="fx"&&n[0]!=="inprogress"&&jQuery.dequeue(this,e)})},dequeue:function(e){return this.each(function(){jQuery.dequeue(this,e)})},clearQueue:function(e){return this.queue(e||"fx",[])},promise:function(e,t){var n,r=1,i=jQuery.Deferred(),s=this,o=this.length,u=function(){--r||i.resolveWith(s,[s])};typeof e!="string"&&(t=e,e=undefined),e=e||"fx";while(o--)n=data_priv.get(s[o],e+"queueHooks"),n&&n.empty&&(r++,n.empty.add(u));return u(),i.promise(t)}});var pnum=/[+-]?(?:\d*\.|)\d+(?:[eE][+-]?\d+|)/.source,cssExpand=["Top","Right","Bottom","Left"],isHidden=function(e,t){return e=t||e,jQuery.css(e,"display")==="none"||!jQuery.contains(e.ownerDocument,e)},rcheckableType=/^(?:checkbox|radio)$/i;(function(){var e=document.createDocumentFragment(),t=e.appendChild(document.createElement("div")),n=document.createElement("input");n.setAttribute("type","radio"),n.setAttribute("checked","checked"),n.setAttribute("name","t"),t.appendChild(n),support.checkClone=t.cloneNode(!0).cloneNode(!0).lastChild.checked,t.innerHTML="<textarea>x</textarea>",support.noCloneChecked=!!t.cloneNode(!0).lastChild.defaultValue})();var strundefined=typeof undefined;support.focusinBubbles="onfocusin"in window;var rkeyEvent=/^key/,rmouseEvent=/^(?:mouse|pointer|contextmenu)|click/,rfocusMorph=/^(?:focusinfocus|focusoutblur)$/,rtypenamespace=/^([^.]*)(?:\.(.+)|)$/;jQuery.event={global:{},add:function(e,t,n,r,i){var s,o,u,a,f,l,c,h,p,d,v,m=data_priv.get(e);if(!m)return;n.handler&&(s=n,n=s.handler,i=s.selector),n.guid||(n.guid=jQuery.guid++),(a=m.events)||(a=m.events={}),(o=m.handle)||(o=m.handle=function(t){return typeof jQuery!==strundefined&&jQuery.event.triggered!==t.type?jQuery.event.dispatch.apply(e,arguments):undefined}),t=(t||"").match(rnotwhite)||[""],f=t.length;while(f--){u=rtypenamespace.exec(t[f])||[],p=v=u[1],d=(u[2]||"").split(".").sort();if(!p)continue;c=jQuery.event.special[p]||{},p=(i?c.delegateType:c.bindType)||p,c=jQuery.event.special[p]||{},l=jQuery.extend({type:p,origType:v,data:r,handler:n,guid:n.guid,selector:i,needsContext:i&&jQuery.expr.match.needsContext.test(i),namespace:d.join(".")},s),(h=a[p])||(h=a[p]=[],h.delegateCount=0,(!c.setup||c.setup.call(e,r,d,o)===!1)&&e.addEventListener&&e.addEventListener(p,o,!1)),c.add&&(c.add.call(e,l),l.handler.guid||(l.handler.guid=n.guid)),i?h.splice(h.delegateCount++,0,l):h.push(l),jQuery.event.global[p]=!0}},remove:function(e,t,n,r,i){var s,o,u,a,f,l,c,h,p,d,v,m=data_priv.hasData(e)&&data_priv.get(e);if(!m||!(a=m.events))return;t=(t||"").match(rnotwhite)||[""],f=t.length;while(f--){u=rtypenamespace.exec(t[f])||[],p=v=u[1],d=(u[2]||"").split(".").sort();if(!p){for(p in a)jQuery.event.remove(e,p+t[f],n,r,!0);continue}c=jQuery.event.special[p]||{},p=(r?c.delegateType:c.bindType)||p,h=a[p]||[],u=u[2]&&new RegExp("(^|\\.)"+d.join("\\.(?:.*\\.|)")+"(\\.|$)"),o=s=h.length;while(s--)l=h[s],(i||v===l.origType)&&(!n||n.guid===l.guid)&&(!u||u.test(l.namespace))&&(!r||r===l.selector||r==="**"&&l.selector)&&(h.splice(s,1),l.selector&&h.delegateCount--,c.remove&&c.remove.call(e,l));o&&!h.length&&((!c.teardown||c.teardown.call(e,d,m.handle)===!1)&&jQuery.removeEvent(e,p,m.handle),delete a[p])}jQuery.isEmptyObject(a)&&(delete m.handle,data_priv.remove(e,"events"))},trigger:function(e,t,n,r){var i,s,o,u,a,f,l,c=[n||document],h=hasOwn.call(e,"type")?e.type:e,p=hasOwn.call(e,"namespace")?e.namespace.split("."):[];s=o=n=n||document;if(n.nodeType===3||n.nodeType===8)return;if(rfocusMorph.test(h+jQuery.event.triggered))return;h.indexOf(".")>=0&&(p=h.split("."),h=p.shift(),p.sort()),a=h.indexOf(":")<0&&"on"+h,e=e[jQuery.expando]?e:new jQuery.Event(h,typeof e=="object"&&e),e.isTrigger=r?2:3,e.namespace=p.join("."),e.namespace_re=e.namespace?new RegExp("(^|\\.)"+p.join("\\.(?:.*\\.|)")+"(\\.|$)"):null,e.result=undefined,e.target||(e.target=n),t=t==null?[e]:jQuery.makeArray(t,[e]),l=jQuery.event.special[h]||{};if(!r&&l.trigger&&l.trigger.apply(n,t)===!1)return;if(!r&&!l.noBubble&&!jQuery.isWindow(n)){u=l.delegateType||h,rfocusMorph.test(u+h)||(s=s.parentNode);for(;s;s=s.parentNode)c.push(s),o=s;o===(n.ownerDocument||document)&&c.push(o.defaultView||o.parentWindow||window)}i=0;while((s=c[i++])&&!e.isPropagationStopped())e.type=i>1?u:l.bindType||h,f=(data_priv.get(s,"events")||{})[e.type]&&data_priv.get(s,"handle"),f&&f.apply(s,t),f=a&&s[a],f&&f.apply&&jQuery.acceptData(s)&&(e.result=f.apply(s,t),e.result===!1&&e.preventDefault());return e.type=h,!r&&!e.isDefaultPrevented()&&(!l._default||l._default.apply(c.pop(),t)===!1)&&jQuery.acceptData(n)&&a&&jQuery.isFunction(n[h])&&!jQuery.isWindow(n)&&(o=n[a],o&&(n[a]=null),jQuery.event.triggered=h,n[h](),jQuery.event.triggered=undefined,o&&(n[a]=o)),e.result},dispatch:function(e){e=jQuery.event.fix(e);var t,n,r,i,s,o=[],u=slice.call(arguments),a=(data_priv.get(this,"events")||{})[e.type]||[],f=jQuery.event.special[e.type]||{};u[0]=e,e.delegateTarget=this;if(f.preDispatch&&f.preDispatch.call(this,e)===!1)return;o=jQuery.event.handlers.call(this,e,a),t=0;while((i=o[t++])&&!e.isPropagationStopped()){e.currentTarget=i.elem,n=0;while((s=i.handlers[n++])&&!e.isImmediatePropagationStopped())if(!e.namespace_re||e.namespace_re.test(s.namespace))e.handleObj=s,e.data=s.data,r=((jQuery.event.special[s.origType]||{}).handle||s.handler).apply(i.elem,u),r!==undefined&&(e.result=r)===!1&&(e.preventDefault(),e.stopPropagation())}return f.postDispatch&&f.postDispatch.call(this,e),e.result},handlers:function(e,t){var n,r,i,s,o=[],u=t.delegateCount,a=e.target;if(u&&a.nodeType&&(!e.button||e.type!=="click"))for(;a!==this;a=a.parentNode||this)if(a.disabled!==!0||e.type!=="click"){r=[];for(n=0;n<u;n++)s=t[n],i=s.selector+" ",r[i]===undefined&&(r[i]=s.needsContext?jQuery(i,this).index(a)>=0:jQuery.find(i,this,null,[a]).length),r[i]&&r.push(s);r.length&&o.push({elem:a,handlers:r})}return u<t.length&&o.push({elem:this,handlers:t.slice(u)}),o},props:"altKey bubbles cancelable ctrlKey currentTarget eventPhase metaKey relatedTarget shiftKey target timeStamp view which".split(" "),fixHooks:{},keyHooks:{props:"char charCode key keyCode".split(" "),filter:function(e,t){return e.which==null&&(e.which=t.charCode!=null?t.charCode:t.keyCode),e}},mouseHooks:{props:"button buttons clientX clientY offsetX offsetY pageX pageY screenX screenY toElement".split(" "),filter:function(e,t){var n,r,i,s=t.button;return e.pageX==null&&t.clientX!=null&&(n=e.target.ownerDocument||document,r=n.documentElement,i=n.body,e.pageX=t.clientX+(r&&r.scrollLeft||i&&i.scrollLeft||0)-(r&&r.clientLeft||i&&i.clientLeft||0),e.pageY=t.clientY+(r&&r.scrollTop||i&&i.scrollTop||0)-(r&&r.clientTop||i&&i.clientTop||0)),!e.which&&s!==undefined&&(e.which=s&1?1:s&2?3:s&4?2:0),e}},fix:function(e){if(e[jQuery.expando])return e;var t,n,r,i=e.type,s=e,o=this.fixHooks[i];o||(this.fixHooks[i]=o=rmouseEvent.test(i)?this.mouseHooks:rkeyEvent.test(i)?this.keyHooks:{}),r=o.props?this.props.concat(o.props):this.props,e=new jQuery.Event(s),t=r.length;while(t--)n=r[t],e[n]=s[n];return e.target||(e.target=document),e.target.nodeType===3&&(e.target=e.target.parentNode),o.filter?o.filter(e,s):e},special:{load:{noBubble:!0},focus:{trigger:function(){if(this!==safeActiveElement()&&this.focus)return this.focus(),!1},delegateType:"focusin"},blur:{trigger:function(){if(this===safeActiveElement()&&this.blur)return this.blur(),!1},delegateType:"focusout"},click:{trigger:function(){if(this.type==="checkbox"&&this.click&&jQuery.nodeName(this,"input"))return this.click(),!1},_default:function(e){return jQuery.nodeName(e.target,"a")}},beforeunload:{postDispatch:function(e){e.result!==undefined&&e.originalEvent&&(e.originalEvent.returnValue=e.result)}}},simulate:function(e,t,n,r){var i=jQuery.extend(new jQuery.Event,n,{type:e,isSimulated:!0,originalEvent:{}});r?jQuery.event.trigger(i,null,t):jQuery.event.dispatch.call(t,i),i.isDefaultPrevented()&&n.preventDefault()}},jQuery.removeEvent=function(e,t,n){e.removeEventListener&&e.removeEventListener(t,n,!1)},jQuery.Event=function(e,t){if(!(this instanceof jQuery.Event))return new jQuery.Event(e,t);e&&e.type?(this.originalEvent=e,this.type=e.type,this.isDefaultPrevented=e.defaultPrevented||e.defaultPrevented===undefined&&e.returnValue===!1?returnTrue:returnFalse):this.type=e,t&&jQuery.extend(this,t),this.timeStamp=e&&e.timeStamp||jQuery.now(),this[jQuery.expando]=!0},jQuery.Event.prototype={isDefaultPrevented:returnFalse,isPropagationStopped:returnFalse,isImmediatePropagationStopped:returnFalse,preventDefault:function(){var e=this.originalEvent;this.isDefaultPrevented=returnTrue,e&&e.preventDefault&&e.preventDefault()},stopPropagation:function(){var e=this.originalEvent;this.isPropagationStopped=returnTrue,e&&e.stopPropagation&&e.stopPropagation()},stopImmediatePropagation:function(){var e=this.originalEvent;this.isImmediatePropagationStopped=returnTrue,e&&e.stopImmediatePropagation&&e.stopImmediatePropagation(),this.stopPropagation()}},jQuery.each({mouseenter:"mouseover",mouseleave:"mouseout",pointerenter:"pointerover",pointerleave:"pointerout"},function(e,t){jQuery.event.special[e]={delegateType:t,bindType:t,handle:function(e){var n,r=this,i=e.relatedTarget,s=e.handleObj;if(!i||i!==r&&!jQuery.contains(r,i))e.type=s.origType,n=s.handler.apply(this,arguments),e.type=t;return n}}}),support.focusinBubbles||jQuery.each({focus:"focusin",blur:"focusout"},function(e,t){var n=function(e){jQuery.event.simulate(t,e.target,jQuery.event.fix(e),!0)};jQuery.event.special[t]={setup:function(){var r=this.ownerDocument||this,i=data_priv.access(r,t);i||r.addEventListener(e,n,!0),data_priv.access(r,t,(i||0)+1)},teardown:function(){var r=this.ownerDocument||this,i=data_priv.access(r,t)-1;i?data_priv.access(r,t,i):(r.removeEventListener(e,n,!0),data_priv.remove(r,t))}}}),jQuery.fn.extend({on:function(e,t,n,r,i){var s,o;if(typeof e=="object"){typeof t!="string"&&(n=n||t,t=undefined);for(o in e)this.on(o,t,n,e[o],i);return this}n==null&&r==null?(r=t,n=t=undefined):r==null&&(typeof t=="string"?(r=n,n=undefined):(r=n,n=t,t=undefined));if(r===!1)r=returnFalse;else if(!r)return this;return i===1&&(s=r,r=function(e){return jQuery().off(e),s.apply(this,arguments)},r.guid=s.guid||(s.guid=jQuery.guid++)),this.each(function(){jQuery.event.add(this,e,r,n,t)})},one:function(e,t,n,r){return this.on(e,t,n,r,1)},off:function(e,t,n){var r,i;if(e&&e.preventDefault&&e.handleObj)return r=e.handleObj,jQuery(e.delegateTarget).off(r.namespace?r.origType+"."+r.namespace:r.origType,r.selector,r.handler),this;if(typeof e=="object"){for(i in e)this.off(i,t,e[i]);return this}if(t===!1||typeof t=="function")n=t,t=undefined;return n===!1&&(n=returnFalse),this.each(function(){jQuery.event.remove(this,e,n,t)})},trigger:function(e,t){return this.each(function(){jQuery.event.trigger(e,t,this)})},triggerHandler:function(e,t){var n=this[0];if(n)return jQuery.event.trigger(e,t,n,!0)}});var rxhtmlTag=/<(?!area|br|col|embed|hr|img|input|link|meta|param)(([\w:]+)[^>]*)\/>/gi,rtagName=/<([\w:]+)/,rhtml=/<|&#?\w+;/,rnoInnerhtml=/<(?:script|style|link)/i,rchecked=/checked\s*(?:[^=]|=\s*.checked.)/i,rscriptType=/^$|\/(?:java|ecma)script/i,rscriptTypeMasked=/^true\/(.*)/,rcleanScript=/^\s*<!(?:\[CDATA\[|--)|(?:\]\]|--)>\s*$/g,wrapMap={option:[1,"<select multiple='multiple'>","</select>"],thead:[1,"<table>","</table>"],col:[2,"<table><colgroup>","</colgroup></table>"],tr:[2,"<table><tbody>","</tbody></table>"],td:[3,"<table><tbody><tr>","</tr></tbody></table>"],_default:[0,"",""]};wrapMap.optgroup=wrapMap.option,wrapMap.tbody=wrapMap.tfoot=wrapMap.colgroup=wrapMap.caption=wrapMap.thead,wrapMap.th=wrapMap.td,jQuery.extend({clone:function(e,t,n){var r,i,s,o,u=e.cloneNode(!0),a=jQuery.contains(e.ownerDocument,e);if(!support.noCloneChecked&&(e.nodeType===1||e.nodeType===11)&&!jQuery.isXMLDoc(e)){o=getAll(u),s=getAll(e);for(r=0,i=s.length;r<i;r++)fixInput(s[r],o[r])}if(t)if(n){s=s||getAll(e),o=o||getAll(u);for(r=0,i=s.length;r<i;r++)cloneCopyEvent(s[r],o[r])}else cloneCopyEvent(e,u);return o=getAll(u,"script"),o.length>0&&setGlobalEval(o,!a&&getAll(e,"script")),u},buildFragment:function(e,t,n,r){var i,s,o,u,a,f,l=t.createDocumentFragment(),c=[],h=0,p=e.length;for(;h<p;h++){i=e[h];if(i||i===0)if(jQuery.type(i)==="object")jQuery.merge(c,i.nodeType?[i]:i);else if(!rhtml.test(i))c.push(t.createTextNode(i));else{s=s||l.appendChild(t.createElement("div")),o=(rtagName.exec(i)||["",""])[1].toLowerCase(),u=wrapMap[o]||wrapMap._default,s.innerHTML=u[1]+i.replace(rxhtmlTag,"<$1></$2>")+u[2],f=u[0];while(f--)s=s.lastChild;jQuery.merge(c,s.childNodes),s=l.firstChild,s.textContent=""}}l.textContent="",h=0;while(i=c[h++]){if(r&&jQuery.inArray(i,r)!==-1)continue;a=jQuery.contains(i.ownerDocument,i),s=getAll(l.appendChild(i),"script"),a&&setGlobalEval(s);if(n){f=0;while(i=s[f++])rscriptType.test(i.type||"")&&n.push(i)}}return l},cleanData:function(e){var t,n,r,i,s=jQuery.event.special,o=0;for(;(n=e[o])!==undefined;o++){if(jQuery.acceptData(n)){i=n[data_priv.expando];if(i&&(t=data_priv.cache[i])){if(t.events)for(r in t.events)s[r]?jQuery.event.remove(n,r):jQuery.removeEvent(n,r,t.handle);data_priv.cache[i]&&delete data_priv.cache[i]}}delete data_user.cache[n[data_user.expando]]}}}),jQuery.fn.extend({text:function(e){return access(this,function(e){return e===undefined?jQuery.text(this):this.empty().each(function(){if(this.nodeType===1||this.nodeType===11||this.nodeType===9)this.textContent=e})},null,e,arguments.length)},append:function(){return this.domManip(arguments,function(e){if(this.nodeType===1||this.nodeType===11||this.nodeType===9){var t=manipulationTarget(this,e);t.appendChild(e)}})},prepend:function(){return this.domManip(arguments,function(e){if(this.nodeType===1||this.nodeType===11||this.nodeType===9){var t=manipulationTarget(this,e);t.insertBefore(e,t.firstChild)}})},before:function(){return this.domManip(arguments,function(e){this.parentNode&&this.parentNode.insertBefore(e,this)})},after:function(){return this.domManip(arguments,function(e){this.parentNode&&this.parentNode.insertBefore(e,this.nextSibling)})},remove:function(e,t){var n,r=e?jQuery.filter(e,this):this,i=0;for(;(n=r[i])!=null;i++)!t&&n.nodeType===1&&jQuery.cleanData(getAll(n)),n.parentNode&&(t&&jQuery.contains(n.ownerDocument,n)&&setGlobalEval(getAll(n,"script")),n.parentNode.removeChild(n));return this},empty:function(){var e,t=0;for(;(e=this[t])!=null;t++)e.nodeType===1&&(jQuery.cleanData(getAll(e,!1)),e.textContent="");return this},clone:function(e,t){return e=e==null?!1:e,t=t==null?e:t,this.map(function(){return jQuery.clone(this,e,t)})},html:function(e){return access(this,function(e){var t=this[0]||{},n=0,r=this.length;if(e===undefined&&t.nodeType===1)return t.innerHTML;if(typeof e=="string"&&!rnoInnerhtml.test(e)&&!wrapMap[(rtagName.exec(e)||["",""])[1].toLowerCase()]){e=e.replace(rxhtmlTag,"<$1></$2>");try{for(;n<r;n++)t=this[n]||{},t.nodeType===1&&(jQuery.cleanData(getAll(t,!1)),t.innerHTML=e);t=0}catch(i){}}t&&this.empty().append(e)},null,e,arguments.length)},replaceWith:function(){var e=arguments[0];return this.domManip(arguments,function(t){e=this.parentNode,jQuery.cleanData(getAll(this)),e&&e.replaceChild(t,this)}),e&&(e.length||e.nodeType)?this:this.remove()},detach:function(e){return this.remove(e,!0)},domManip:function(e,t){e=concat.apply([],e);var n,r,i,s,o,u,a=0,f=this.length,l=this,c=f-1,h=e[0],p=jQuery.isFunction(h);if(p||f>1&&typeof h=="string"&&!support.checkClone&&rchecked.test(h))return this.each(function(n){var r=l.eq(n);p&&(e[0]=h.call(this,n,r.html())),r.domManip(e,t)});if(f){n=jQuery.buildFragment(e,this[0].ownerDocument,!1,this),r=n.firstChild,n.childNodes.length===1&&(n=r);if(r){i=jQuery.map(getAll(n,"script"),disableScript),s=i.length;for(;a<f;a++)o=n,a!==c&&(o=jQuery.clone(o,!0,!0),s&&jQuery.merge(i,getAll(o,"script"))),t.call(this[a],o,a);if(s){u=i[i.length-1].ownerDocument,jQuery.map(i,restoreScript);for(a=0;a<s;a++)o=i[a],rscriptType.test(o.type||"")&&!data_priv.access(o,"globalEval")&&jQuery.contains(u,o)&&(o.src?jQuery._evalUrl&&jQuery._evalUrl(o.src):jQuery.globalEval(o.textContent.replace(rcleanScript,"")))}}}return this}}),jQuery.each({appendTo:"append",prependTo:"prepend",insertBefore:"before",insertAfter:"after",replaceAll:"replaceWith"},function(e,t){jQuery.fn[e]=function(e){var n,r=[],i=jQuery(e),s=i.length-1,o=0;for(;o<=s;o++)n=o===s?this:this.clone(!0),jQuery(i[o])[t](n),push.apply(r,n.get());return this.pushStack(r)}});var iframe,elemdisplay={},rmargin=/^margin/,rnumnonpx=new RegExp("^("+pnum+")(?!px)[a-z%]+$","i"),getStyles=function(e){return e.ownerDocument.defaultView.opener?e.ownerDocument.defaultView.getComputedStyle(e,null):window.getComputedStyle(e,null)};(function(){function s(){i.style.cssText="-webkit-box-sizing:border-box;-moz-box-sizing:border-box;box-sizing:border-box;display:block;margin-top:1%;top:1%;border:1px;padding:1px;width:4px;position:absolute",i.innerHTML="",n.appendChild(r);var s=window.getComputedStyle(i,null);e=s.top!=="1%",t=s.width==="4px",n.removeChild(r)}var e,t,n=document.documentElement,r=document.createElement("div"),i=document.createElement("div");if(!i.style)return;i.style.backgroundClip="content-box",i.cloneNode(!0).style.backgroundClip="",support.clearCloneStyle=i.style.backgroundClip==="content-box",r.style.cssText="border:0;width:0;height:0;top:0;left:-9999px;margin-top:1px;position:absolute",r.appendChild(i),window.getComputedStyle&&jQuery.extend(support,{pixelPosition:function(){return s(),e},boxSizingReliable:function(){return t==null&&s(),t},reliableMarginRight:function(){var e,t=i.appendChild(document.createElement("div"));return t.style.cssText=i.style.cssText="-webkit-box-sizing:content-box;-moz-box-sizing:content-box;box-sizing:content-box;display:block;margin:0;border:0;padding:0",t.style.marginRight=t.style.width="0",i.style.width="1px",n.appendChild(r),e=!parseFloat(window.getComputedStyle(t,null).marginRight),n.removeChild(r),i.removeChild(t),e}})})(),jQuery.swap=function(e,t,n,r){var i,s,o={};for(s in t)o[s]=e.style[s],e.style[s]=t[s];i=n.apply(e,r||[]);for(s in t)e.style[s]=o[s];return i};var rdisplayswap=/^(none|table(?!-c[ea]).+)/,rnumsplit=new RegExp("^("+pnum+")(.*)$","i"),rrelNum=new RegExp("^([+-])=("+pnum+")","i"),cssShow={position:"absolute",visibility:"hidden",display:"block"},cssNormalTransform={letterSpacing:"0",fontWeight:"400"},cssPrefixes=["Webkit","O","Moz","ms"];jQuery.extend({cssHooks:{opacity:{get:function(e,t){if(t){var n=curCSS(e,"opacity");return n===""?"1":n}}}},cssNumber:{columnCount:!0,fillOpacity:!0,flexGrow:!0,flexShrink:!0,fontWeight:!0,lineHeight:!0,opacity:!0,order:!0,orphans:!0,widows:!0,zIndex:!0,zoom:!0},cssProps:{"float":"cssFloat"},style:function(e,t,n,r){if(!e||e.nodeType===3||e.nodeType===8||!e.style)return;var i,s,o,u=jQuery.camelCase(t),a=e.style;t=jQuery.cssProps[u]||(jQuery.cssProps[u]=vendorPropName(a,u)),o=jQuery.cssHooks[t]||jQuery.cssHooks[u];if(n===undefined)return o&&"get"in o&&(i=o.get(e,!1,r))!==undefined?i:a[t];s=typeof n,s==="string"&&(i=rrelNum.exec(n))&&(n=(i[1]+1)*i[2]+parseFloat(jQuery.css(e,t)),s="number");if(n==null||n!==n)return;s==="number"&&!jQuery.cssNumber[u]&&(n+="px"),!support.clearCloneStyle&&n===""&&t.indexOf("background")===0&&(a[t]="inherit");if(!o||!("set"in o)||(n=o.set(e,n,r))!==undefined)a[t]=n},css:function(e,t,n,r){var i,s,o,u=jQuery.camelCase(t);return t=jQuery.cssProps[u]||(jQuery.cssProps[u]=vendorPropName(e.style,u)),o=jQuery.cssHooks[t]||jQuery.cssHooks[u],o&&"get"in o&&(i=o.get(e,!0,n)),i===undefined&&(i=curCSS(e,t,r)),i==="normal"&&t in cssNormalTransform&&(i=cssNormalTransform[t]),n===""||n?(s=parseFloat(i),n===!0||jQuery.isNumeric(s)?s||0:i):i}}),jQuery.each(["height","width"],function(e,t){jQuery.cssHooks[t]={get:function(e,n,r){if(n)return rdisplayswap.test(jQuery.css(e,"display"))&&e.offsetWidth===0?jQuery.swap(e,cssShow,function(){return getWidthOrHeight(e,t,r)}):getWidthOrHeight(e,t,r)},set:function(e,n,r){var i=r&&getStyles(e);return setPositiveNumber(e,n,r?augmentWidthOrHeight(e,t,r,jQuery.css(e,"boxSizing",!1,i)==="border-box",i):0)}}}),jQuery.cssHooks.marginRight=addGetHookIf(support.reliableMarginRight,function(e,t){if(t)return jQuery.swap(e,{display:"inline-block"},curCSS,[e,"marginRight"])}),jQuery.each({margin:"",padding:"",border:"Width"},function(e,t){jQuery.cssHooks[e+t]={expand:function(n){var r=0,i={},s=typeof n=="string"?n.split(" "):[n];for(;r<4;r++)i[e+cssExpand[r]+t]=s[r]||s[r-2]||s[0];return i}},rmargin.test(e)||(jQuery.cssHooks[e+t].set=setPositiveNumber)}),jQuery.fn.extend({css:function(e,t){return access(this,function(e,t,n){var r,i,s={},o=0;if(jQuery.isArray(t)){r=getStyles(e),i=t.length;for(;o<i;o++)s[t[o]]=jQuery.css(e,t[o],!1,r);return s}return n!==undefined?jQuery.style(e,t,n):jQuery.css(e,t)},e,t,arguments.length>1)},show:function(){return showHide(this,!0)},hide:function(){return showHide(this)},toggle:function(e){return typeof e=="boolean"?e?this.show():this.hide():this.each(function(){isHidden(this)?jQuery(this).show():jQuery(this).hide()})}}),jQuery.Tween=Tween,Tween.prototype={constructor:Tween,init:function(e,t,n,r,i,s){this.elem=e,this.prop=n,this.easing=i||"swing",this.options=t,this.start=this.now=this.cur(),this.end=r,this.unit=s||(jQuery.cssNumber[n]?"":"px")},cur:function(){var e=Tween.propHooks[this.prop];return e&&e.get?e.get(this):Tween.propHooks._default.get(this)},run:function(e){var t,n=Tween.propHooks[this.prop];return this.options.duration?this.pos=t=jQuery.easing[this.easing](e,this.options.duration*e,0,1,this.options.duration):this.pos=t=e,this.now=(this.end-this.start)*t+this.start,this.options.step&&this.options.step.call(this.elem,this.now,this),n&&n.set?n.set(this):Tween.propHooks._default.set(this),this}},Tween.prototype.init.prototype=Tween.prototype,Tween.propHooks={_default:{get:function(e){var t;return e.elem[e.prop]==null||!!e.elem.style&&e.elem.style[e.prop]!=null?(t=jQuery.css(e.elem,e.prop,""),!t||t==="auto"?0:t):e.elem[e.prop]},set:function(e){jQuery.fx.step[e.prop]?jQuery.fx.step[e.prop](e):e.elem.style&&(e.elem.style[jQuery.cssProps[e.prop]]!=null||jQuery.cssHooks[e.prop])?jQuery.style(e.elem,e.prop,e.now+e.unit):e.elem[e.prop]=e.now}}},Tween.propHooks.scrollTop=Tween.propHooks.scrollLeft={set:function(e){e.elem.nodeType&&e.elem.parentNode&&(e.elem[e.prop]=e.now)}},jQuery.easing={linear:function(e){return e},swing:function(e){return.5-Math.cos(e*Math.PI)/2}},jQuery.fx=Tween.prototype.init,jQuery.fx.step={};var fxNow,timerId,rfxtypes=/^(?:toggle|show|hide)$/,rfxnum=new RegExp("^(?:([+-])=|)("+pnum+")([a-z%]*)$","i"),rrun=/queueHooks$/,animationPrefilters=[defaultPrefilter],tweeners={"*":[function(e,t){var n=this.createTween(e,t),r=n.cur(),i=rfxnum.exec(t),s=i&&i[3]||(jQuery.cssNumber[e]?"":"px"),o=(jQuery.cssNumber[e]||s!=="px"&&+r)&&rfxnum.exec(jQuery.css(n.elem,e)),u=1,a=20;if(o&&o[3]!==s){s=s||o[3],i=i||[],o=+r||1;do u=u||".5",o/=u,jQuery.style(n.elem,e,o+s);while(u!==(u=n.cur()/r)&&u!==1&&--a)}return i&&(o=n.start=+o||+r||0,n.unit=s,n.end=i[1]?o+(i[1]+1)*i[2]:+i[2]),n}]};jQuery.Animation=jQuery.extend(Animation,{tweener:function(e,t){jQuery.isFunction(e)?(t=e,e=["*"]):e=e.split(" ");var n,r=0,i=e.length;for(;r<i;r++)n=e[r],tweeners[n]=tweeners[n]||[],tweeners[n].unshift(t)},prefilter:function(e,t){t?animationPrefilters.unshift(e):animationPrefilters.push(e)}}),jQuery.speed=function(e,t,n){var r=e&&typeof e=="object"?jQuery.extend({},e):{complete:n||!n&&t||jQuery.isFunction(e)&&e,duration:e,easing:n&&t||t&&!jQuery.isFunction(t)&&t};r.duration=jQuery.fx.off?0:typeof r.duration=="number"?r.duration:r.duration in jQuery.fx.speeds?jQuery.fx.speeds[r.duration]:jQuery.fx.speeds._default;if(r.queue==null||r.queue===!0)r.queue="fx";return r.old=r.complete,r.complete=function(){jQuery.isFunction(r.old)&&r.old.call(this),r.queue&&jQuery.dequeue(this,r.queue)},r},jQuery.fn.extend({fadeTo:function(e,t,n,r){return this.filter(isHidden).css("opacity",0).show().end().animate({opacity:t},e,n,r)},animate:function(e,t,n,r){var i=jQuery.isEmptyObject(e),s=jQuery.speed(t,n,r),o=function(){var t=Animation(this,jQuery.extend({},e),s);(i||data_priv.get(this,"finish"))&&t.stop(!0)};return o.finish=o,i||s.queue===!1?this.each(o):this.queue(s.queue,o)},stop:function(e,t,n){var r=function(e){var t=e.stop;delete e.stop,t(n)};return typeof e!="string"&&(n=t,t=e,e=undefined),t&&e!==!1&&this.queue(e||"fx",[]),this.each(function(){var t=!0,i=e!=null&&e+"queueHooks",s=jQuery.timers,o=data_priv.get(this);if(i)o[i]&&o[i].stop&&r(o[i]);else for(i in o)o[i]&&o[i].stop&&rrun.test(i)&&r(o[i]);for(i=s.length;i--;)s[i].elem===this&&(e==null||s[i].queue===e)&&(s[i].anim.stop(n),t=!1,s.splice(i,1));(t||!n)&&jQuery.dequeue(this,e)})},finish:function(e){return e!==!1&&(e=e||"fx"),this.each(function(){var t,n=data_priv.get(this),r=n[e+"queue"],i=n[e+"queueHooks"],s=jQuery.timers,o=r?r.length:0;n.finish=!0,jQuery.queue(this,e,[]),i&&i.stop&&i.stop.call(this,!0);for(t=s.length;t--;)s[t].elem===this&&s[t].queue===e&&(s[t].anim.stop(!0),s.splice(t,1));for(t=0;t<o;t++)r[t]&&r[t].finish&&r[t].finish.call(this);delete n.finish})}}),jQuery.each(["toggle","show","hide"],function(e,t){var n=jQuery.fn[t];jQuery.fn[t]=function(e,r,i){return e==null||typeof e=="boolean"?n.apply(this,arguments):this.animate(genFx(t,!0),e,r,i)}}),jQuery.each({slideDown:genFx("show"),slideUp:genFx("hide"),slideToggle:genFx("toggle"),fadeIn:{opacity:"show"},fadeOut:{opacity:"hide"},fadeToggle:{opacity:"toggle"}},function(e,t){jQuery.fn[e]=function(e,n,r){return this.animate(t,e,n,r)}}),jQuery.timers=[],jQuery.fx.tick=function(){var e,t=0,n=jQuery.timers;fxNow=jQuery.now();for(;t<n.length;t++)e=n[t],!e()&&n[t]===e&&n.splice(t--,1);n.length||jQuery.fx.stop(),fxNow=undefined},jQuery.fx.timer=function(e){jQuery.timers.push(e),e()?jQuery.fx.start():jQuery.timers.pop()},jQuery.fx.interval=13,jQuery.fx.start=function(){timerId||(timerId=setInterval(jQuery.fx.tick,jQuery.fx.interval))},jQuery.fx.stop=function(){clearInterval(timerId),timerId=null},jQuery.fx.speeds={slow:600,fast:200,_default:400},jQuery.fn.delay=function(e,t){return e=jQuery.fx?jQuery.fx.speeds[e]||e:e,t=t||"fx",this.queue(t,function(t,n){var r=setTimeout(t,e);n.stop=function(){clearTimeout(r)}})},function(){var e=document.createElement("input"),t=document.createElement("select"),n=t.appendChild(document.createElement("option"));e.type="checkbox",support.checkOn=e.value!=="",support.optSelected=n.selected,t.disabled=!0,support.optDisabled=!n.disabled,e=document.createElement("input"),e.value="t",e.type="radio",support.radioValue=e.value==="t"}();var nodeHook,boolHook,attrHandle=jQuery.expr.attrHandle;jQuery.fn.extend({attr:function(e,t){return access(this,jQuery.attr,e,t,arguments.length>1)},removeAttr:function(e){return this.each(function(){jQuery.removeAttr(this,e)})}}),jQuery.extend({attr:function(e,t,n){var r,i,s=e.nodeType;if(!e||s===3||s===8||s===2)return;if(typeof e.getAttribute===strundefined)return jQuery.prop(e,t,n);if(s!==1||!jQuery.isXMLDoc(e))t=t.toLowerCase(),r=jQuery.attrHooks[t]||(jQuery.expr.match.bool.test(t)?boolHook:nodeHook);if(n===undefined)return r&&"get"in r&&(i=r.get(e,t))!==null?i:(i=jQuery.find.attr(e,t),i==null?undefined:i);if(n!==null)return r&&"set"in r&&(i=r.set(e,n,t))!==undefined?i:(e.setAttribute(t,n+""),n);jQuery.removeAttr(e,t)},removeAttr:function(e,t){var n,r,i=0,s=t&&t.match(rnotwhite);if(s&&e.nodeType===1)while(n=s[i++])r=jQuery.propFix[n]||n,jQuery.expr.match.bool.test(n)&&(e[r]=!1),e.removeAttribute(n)},attrHooks:{type:{set:function(e,t){if(!support.radioValue&&t==="radio"&&jQuery.nodeName(e,"input")){var n=e.value;return e.setAttribute("type",t),n&&(e.value=n),t}}}}}),boolHook={set:function(e,t,n){return t===!1?jQuery.removeAttr(e,n):e.setAttribute(n,n),n}},jQuery.each(jQuery.expr.match.bool.source.match(/\w+/g),function(e,t){var n=attrHandle[t]||jQuery.find.attr;attrHandle[t]=function(e,t,r){var i,s;return r||(s=attrHandle[t],attrHandle[t]=i,i=n(e,t,r)!=null?t.toLowerCase():null,attrHandle[t]=s),i}});var rfocusable=/^(?:input|select|textarea|button)$/i;jQuery.fn.extend({prop:function(e,t){return access(this,jQuery.prop,e,t,arguments.length>1)},removeProp:function(e){return this.each(function(){delete this[jQuery.propFix[e]||e]})}}),jQuery.extend({propFix:{"for":"htmlFor","class":"className"},prop:function(e,t,n){var r,i,s,o=e.nodeType;if(!e||o===3||o===8||o===2)return;return s=o!==1||!jQuery.isXMLDoc(e),s&&(t=jQuery.propFix[t]||t,i=jQuery.propHooks[t]),n!==undefined?i&&"set"in i&&(r=i.set(e,n,t))!==undefined?r:e[t]=n:i&&"get"in i&&(r=i.get(e,t))!==null?r:e[t]},propHooks:{tabIndex:{get:function(e){return e.hasAttribute("tabindex")||rfocusable.test(e.nodeName)||e.href?e.tabIndex:-1}}}}),support.optSelected||(jQuery.propHooks.selected={get:function(e){var t=e.parentNode;return t&&t.parentNode&&t.parentNode.selectedIndex,null}}),jQuery.each(["tabIndex","readOnly","maxLength","cellSpacing","cellPadding","rowSpan","colSpan","useMap","frameBorder","contentEditable"],function(){jQuery.propFix[this.toLowerCase()]=this});var rclass=/[\t\r\n\f]/g;jQuery.fn.extend({addClass:function(e){var t,n,r,i,s,o,u=typeof e=="string"&&e,a=0,f=this.length;if(jQuery.isFunction(e))return this.each(function(t){jQuery(this).addClass(e.call(this,t,this.className))});if(u){t=(e||"").match(rnotwhite)||[];for(;a<f;a++){n=this[a],r=n.nodeType===1&&(n.className?(" "+n.className+" ").replace(rclass," "):" ");if(r){s=0;while(i=t[s++])r.indexOf(" "+i+" ")<0&&(r+=i+" ");o=jQuery.trim(r),n.className!==o&&(n.className=o)}}}return this},removeClass:function(e){var t,n,r,i,s,o,u=arguments.length===0||typeof e=="string"&&e,a=0,f=this.length;if(jQuery.isFunction(e))return this.each(function(t){jQuery(this).removeClass(e.call(this,t,this.className))});if(u){t=(e||"").match(rnotwhite)||[];for(;a<f;a++){n=this[a],r=n.nodeType===1&&(n.className?(" "+n.className+" ").replace(rclass," "):"");if(r){s=0;while(i=t[s++])while(r.indexOf(" "+i+" ")>=0)r=r.replace(" "+i+" "," ");o=e?jQuery.trim(r):"",n.className!==o&&(n.className=o)}}}return this},toggleClass:function(e,t){var n=typeof e;return typeof t=="boolean"&&n==="string"?t?this.addClass(e):this.removeClass(e):jQuery.isFunction(e)?this.each(function(n){jQuery(this).toggleClass(e.call(this,n,this.className,t),t)}):this.each(function(){if(n==="string"){var t,r=0,i=jQuery(this),s=e.match(rnotwhite)||[];while(t=s[r++])i.hasClass(t)?i.removeClass(t):i.addClass(t)}else if(n===strundefined||n==="boolean")this.className&&data_priv.set(this,"__className__",this.className),this.className=this.className||e===!1?"":data_priv.get(this,"__className__")||""})},hasClass:function(e){var t=" "+e+" ",n=0,r=this.length;for(;n<r;n++)if(this[n].nodeType===1&&(" "+this[n].className+" ").replace(rclass," ").indexOf(t)>=0)return!0;return!1}});var rreturn=/\r/g;jQuery.fn.extend({val:function(e){var t,n,r,i=this[0];if(!arguments.length){if(i)return t=jQuery.valHooks[i.type]||jQuery.valHooks[i.nodeName.toLowerCase()],t&&"get"in t&&(n=t.get(i,"value"))!==undefined?n:(n=i.value,typeof n=="string"?n.replace(rreturn,""):n==null?"":n);return}return r=jQuery.isFunction(e),this.each(function(n){var i;if(this.nodeType!==1)return;r?i=e.call(this,n,jQuery(this).val()):i=e,i==null?i="":typeof i=="number"?i+="":jQuery.isArray(i)&&(i=jQuery.map(i,function(e){return e==null?"":e+""})),t=jQuery.valHooks[this.type]||jQuery.valHooks[this.nodeName.toLowerCase()];if(!t||!("set"in t)||t.set(this,i,"value")===undefined)this.value=i})}}),jQuery.extend({valHooks:{option:{get:function(e){var t=jQuery.find.attr(e,"value");return t!=null?t:jQuery.trim(jQuery.text(e))}},select:{get:function(e){var t,n,r=e.options,i=e.selectedIndex,s=e.type==="select-one"||i<0,o=s?null:[],u=s?i+1:r.length,a=i<0?u:s?i:0;for(;a<u;a++){n=r[a];if((n.selected||a===i)&&(support.optDisabled?!n.disabled:n.getAttribute("disabled")===null)&&(!n.parentNode.disabled||!jQuery.nodeName(n.parentNode,"optgroup"))){t=jQuery(n).val();if(s)return t;o.push(t)}}return o},set:function(e,t){var n,r,i=e.options,s=jQuery.makeArray(t),o=i.length;while(o--){r=i[o];if(r.selected=jQuery.inArray(r.value,s)>=0)n=!0}return n||(e.selectedIndex=-1),s}}}}),jQuery.each(["radio","checkbox"],function(){jQuery.valHooks[this]={set:function(e,t){if(jQuery.isArray(t))return e.checked=jQuery.inArray(jQuery(e).val(),t)>=0}},support.checkOn||(jQuery.valHooks[this].get=function(e){return e.getAttribute("value")===null?"on":e.value})}),jQuery.each("blur focus focusin focusout load resize scroll unload click dblclick mousedown mouseup mousemove mouseover mouseout mouseenter mouseleave change select submit keydown keypress keyup error contextmenu".split(" "),function(e,t){jQuery.fn[t]=function(e,n){return arguments.length>0?this.on(t,null,e,n):this.trigger(t)}}),jQuery.fn.extend({hover:function(e,t){return this.mouseenter(e).mouseleave(t||e)},bind:function(e,t,n){return this.on(e,null,t,n)},unbind:function(e,t){return this.off(e,null,t)},delegate:function(e,t,n,r){return this.on(t,e,n,r)},undelegate:function(e,t,n){return arguments.length===1?this.off(e,"**"):this.off(t,e||"**",n)}});var nonce=jQuery.now(),rquery=/\?/;jQuery.parseJSON=function(e){return JSON.parse(e+"")},jQuery.parseXML=function(e){var t,n;if(!e||typeof e!="string")return null;try{n=new DOMParser,t=n.parseFromString(e,"text/xml")}catch(r){t=undefined}return(!t||t.getElementsByTagName("parsererror").length)&&jQuery.error("Invalid XML: "+e),t};var rhash=/#.*$/,rts=/([?&])_=[^&]*/,rheaders=/^(.*?):[ \t]*([^\r\n]*)$/mg,rlocalProtocol=/^(?:about|app|app-storage|.+-extension|file|res|widget):$/,rnoContent=/^(?:GET|HEAD)$/,rprotocol=/^\/\//,rurl=/^([\w.+-]+:)(?:\/\/(?:[^\/?#]*@|)([^\/?#:]*)(?::(\d+)|)|)/,prefilters={},transports={},allTypes="*/".concat("*"),ajaxLocation=window.location.href,ajaxLocParts=rurl.exec(ajaxLocation.toLowerCase())||[];jQuery.extend({active:0,lastModified:{},etag:{},ajaxSettings:{url:ajaxLocation,type:"GET",isLocal:rlocalProtocol.test(ajaxLocParts[1]),global:!0,processData:!0,async:!0,contentType:"application/x-www-form-urlencoded; charset=UTF-8",accepts:{"*":allTypes,text:"text/plain",html:"text/html",xml:"application/xml, text/xml",json:"application/json, text/javascript"},contents:{xml:/xml/,html:/html/,json:/json/},responseFields:{xml:"responseXML",text:"responseText",json:"responseJSON"},converters:{"* text":String,"text html":!0,"text json":jQuery.parseJSON,"text xml":jQuery.parseXML},flatOptions:{url:!0,context:!0}},ajaxSetup:function(e,t){return t?ajaxExtend(ajaxExtend(e,jQuery.ajaxSettings),t):ajaxExtend(jQuery.ajaxSettings,e)},ajaxPrefilter:addToPrefiltersOrTransports(prefilters),ajaxTransport:addToPrefiltersOrTransports(transports),ajax:function(e,t){function S(e,t,s,u){var f,m,g,b,E,S=t;if(y===2)return;y=2,o&&clearTimeout(o),n=undefined,i=u||"",w.readyState=e>0?4:0,f=e>=200&&e<300||e===304,s&&(b=ajaxHandleResponses(l,w,s)),b=ajaxConvert(l,b,w,f);if(f)l.ifModified&&(E=w.getResponseHeader("Last-Modified"),E&&(jQuery.lastModified[r]=E),E=w.getResponseHeader("etag"),E&&(jQuery.etag[r]=E)),e===204||l.type==="HEAD"?S="nocontent":e===304?S="notmodified":(S=b.state,m=b.data,g=b.error,f=!g);else{g=S;if(e||!S)S="error",e<0&&(e=0)}w.status=e,w.statusText=(t||S)+"",f?p.resolveWith(c,[m,S,w]):p.rejectWith(c,[w,S,g]),w.statusCode(v),v=undefined,a&&h.trigger(f?"ajaxSuccess":"ajaxError",[w,l,f?m:g]),d.fireWith(c,[w,S]),a&&(h.trigger("ajaxComplete",[w,l]),--jQuery.active||jQuery.event.trigger("ajaxStop"))}typeof e=="object"&&(t=e,e=undefined),t=t||{};var n,r,i,s,o,u,a,f,l=jQuery.ajaxSetup({},t),c=l.context||l,h=l.context&&(c.nodeType||c.jquery)?jQuery(c):jQuery.event,p=jQuery.Deferred(),d=jQuery.Callbacks("once memory"),v=l.statusCode||{},m={},g={},y=0,b="canceled",w={readyState:0,getResponseHeader:function(e){var t;if(y===2){if(!s){s={};while(t=rheaders.exec(i))s[t[1].toLowerCase()]=t[2]}t=s[e.toLowerCase()]}return t==null?null:t},getAllResponseHeaders:function(){return y===2?i:null},setRequestHeader:function(e,t){var n=e.toLowerCase();return y||(e=g[n]=g[n]||e,m[e]=t),this},overrideMimeType:function(e){return y||(l.mimeType=e),this},statusCode:function(e){var t;if(e)if(y<2)for(t in e)v[t]=[v[t],e[t]];else w.always(e[w.status]);return this},abort:function(e){var t=e||b;return n&&n.abort(t),S(0,t),this}};p.promise(w).complete=d.add,w.success=w.done,w.error=w.fail,l.url=((e||l.url||ajaxLocation)+"").replace(rhash,"").replace(rprotocol,ajaxLocParts[1]+"//"),l.type=t.method||t.type||l.method||l.type,l.dataTypes=jQuery.trim(l.dataType||"*").toLowerCase().match(rnotwhite)||[""],l.crossDomain==null&&(u=rurl.exec(l.url.toLowerCase()),l.crossDomain=!(!u||u[1]===ajaxLocParts[1]&&u[2]===ajaxLocParts[2]&&(u[3]||(u[1]==="http:"?"80":"443"))===(ajaxLocParts[3]||(ajaxLocParts[1]==="http:"?"80":"443")))),l.data&&l.processData&&typeof l.data!="string"&&(l.data=jQuery.param(l.data,l.traditional)),inspectPrefiltersOrTransports(prefilters,l,t,w);if(y===2)return w;a=jQuery.event&&l.global,a&&jQuery.active++===0&&jQuery.event.trigger("ajaxStart"),l.type=l.type.toUpperCase(),l.hasContent=!rnoContent.test(l.type),r=l.url,l.hasContent||(l.data&&(r=l.url+=(rquery.test(r)?"&":"?")+l.data,delete l.data),l.cache===!1&&(l.url=rts.test(r)?r.replace(rts,"$1_="+nonce++):r+(rquery.test(r)?"&":"?")+"_="+nonce++)),l.ifModified&&(jQuery.lastModified[r]&&w.setRequestHeader("If-Modified-Since",jQuery.lastModified[r]),jQuery.etag[r]&&w.setRequestHeader("If-None-Match",jQuery.etag[r])),(l.data&&l.hasContent&&l.contentType!==!1||t.contentType)&&w.setRequestHeader("Content-Type",l.contentType),w.setRequestHeader("Accept",l.dataTypes[0]&&l.accepts[l.dataTypes[0]]?l.accepts[l.dataTypes[0]]+(l.dataTypes[0]!=="*"?", "+allTypes+"; q=0.01":""):l.accepts["*"]);for(f in l.headers)w.setRequestHeader(f,l.headers[f]);if(!l.beforeSend||l.beforeSend.call(c,w,l)!==!1&&y!==2){b="abort";for(f in{success:1,error:1,complete:1})w[f](l[f]);n=inspectPrefiltersOrTransports(transports,l,t,w);if(!n)S(-1,"No Transport");else{w.readyState=1,a&&h.trigger("ajaxSend",[w,l]),l.async&&l.timeout>0&&(o=setTimeout(function(){w.abort("timeout")},l.timeout));try{y=1,n.send(m,S)}catch(E){if(!(y<2))throw E;S(-1,E)}}return w}return w.abort()},getJSON:function(e,t,n){return jQuery.get(e,t,n,"json")},getScript:function(e,t){return jQuery.get(e,undefined,t,"script")}}),jQuery.each(["get","post"],function(e,t){jQuery[t]=function(e,n,r,i){return jQuery.isFunction(n)&&(i=i||r,r=n,n=undefined),jQuery.ajax({url:e,type:t,dataType:i,data:n,success:r})}}),jQuery._evalUrl=function(e){return jQuery.ajax({url:e,type:"GET",dataType:"script",async:!1,global:!1,"throws":!0})},jQuery.fn.extend({wrapAll:function(e){var t;return jQuery.isFunction(e)?this.each(function(t){jQuery(this).wrapAll(e.call(this,t))}):(this[0]&&(t=jQuery(e,this[0].ownerDocument).eq(0).clone(!0),this[0].parentNode&&t.insertBefore(this[0]),t.map(function(){var e=this;while(e.firstElementChild)e=e.firstElementChild;return e}).append(this)),this)},wrapInner:function(e){return jQuery.isFunction(e)?this.each(function(t){jQuery(this).wrapInner(e.call(this,t))}):this.each(function(){var t=jQuery(this),n=t.contents();n.length?n.wrapAll(e):t.append(e)})},wrap:function(e){var t=jQuery.isFunction(e);return this.each(function(n){jQuery(this).wrapAll(t?e.call(this,n):e)})},unwrap:function(){return this.parent().each(function(){jQuery.nodeName(this,"body")||jQuery(this).replaceWith(this.childNodes)}).end()}}),jQuery.expr.filters.hidden=function(e){return e.offsetWidth<=0&&e.offsetHeight<=0},jQuery.expr.filters.visible=function(e){return!jQuery.expr.filters.hidden(e)};var r20=/%20/g,rbracket=/\[\]$/,rCRLF=/\r?\n/g,rsubmitterTypes=/^(?:submit|button|image|reset|file)$/i,rsubmittable=/^(?:input|select|textarea|keygen)/i;jQuery.param=function(e,t){var n,r=[],i=function(e,t){t=jQuery.isFunction(t)?t():t==null?"":t,r[r.length]=encodeURIComponent(e)+"="+encodeURIComponent(t)};t===undefined&&(t=jQuery.ajaxSettings&&jQuery.ajaxSettings.traditional);if(jQuery.isArray(e)||e.jquery&&!jQuery.isPlainObject(e))jQuery.each(e,function(){i(this.name,this.value)});else for(n in e)buildParams(n,e[n],t,i);return r.join("&").replace(r20,"+")},jQuery.fn.extend({serialize:function(){return jQuery.param(this.serializeArray())},serializeArray:function(){return this.map(function(){var e=jQuery.prop(this,"elements");return e?jQuery.makeArray(e):this}).filter(function(){var e=this.type;return this.name&&!jQuery(this).is(":disabled")&&rsubmittable.test(this.nodeName)&&!rsubmitterTypes.test(e)&&(this.checked||!rcheckableType.test(e))}).map(function(e,t){var n=jQuery(this).val();return n==null?null:jQuery.isArray(n)?jQuery.map(n,function(e){return{name:t.name,value:e.replace(rCRLF,"\r\n")}}):{name:t.name,value:n.replace(rCRLF,"\r\n")}}).get()}}),jQuery.ajaxSettings.xhr=function(){try{return new XMLHttpRequest}catch(e){}};var xhrId=0,xhrCallbacks={},xhrSuccessStatus={0:200,1223:204},xhrSupported=jQuery.ajaxSettings.xhr();window.attachEvent&&window.attachEvent("onunload",function(){for(var e in xhrCallbacks)xhrCallbacks[e]()}),support.cors=!!xhrSupported&&"withCredentials"in xhrSupported,support.ajax=xhrSupported=!!xhrSupported,jQuery.ajaxTransport(function(e){var t;if(support.cors||xhrSupported&&!e.crossDomain)return{send:function(n,r){var i,s=e.xhr(),o=++xhrId;s.open(e.type,e.url,e.async,e.username,e.password);if(e.xhrFields)for(i in e.xhrFields)s[i]=e.xhrFields[i];e.mimeType&&s.overrideMimeType&&s.overrideMimeType(e.mimeType),!e.crossDomain&&!n["X-Requested-With"]&&(n["X-Requested-With"]="XMLHttpRequest");for(i in n)s.setRequestHeader(i,n[i]);t=function(e){return function(){t&&(delete xhrCallbacks[o],t=s.onload=s.onerror=null,e==="abort"?s.abort():e==="error"?r(s.status,s.statusText):r(xhrSuccessStatus[s.status]||s.status,s.statusText,typeof s.responseText=="string"?{text:s.responseText}:undefined,s.getAllResponseHeaders()))}},s.onload=t(),s.onerror=t("error"),t=xhrCallbacks[o]=t("abort");try{s.send(e.hasContent&&e.data||null)}catch(u){if(t)throw u}},abort:function(){t&&t()}}}),jQuery.ajaxSetup({accepts:{script:"text/javascript, application/javascript, application/ecmascript, application/x-ecmascript"},contents:{script:/(?:java|ecma)script/},converters:{"text script":function(e){return jQuery.globalEval(e),e}}}),jQuery.ajaxPrefilter("script",function(e){e.cache===undefined&&(e.cache=!1),e.crossDomain&&(e.type="GET")}),jQuery.ajaxTransport("script",function(e){if(e.crossDomain){var t,n;return{send:function(r,i){t=jQuery("<script>").prop({async:!0,charset:e.scriptCharset,src:e.url}).on("load error",n=function(e){t.remove(),n=null,e&&i(e.type==="error"?404:200,e.type)}),document.head.appendChild(t[0])},abort:function(){n&&n()}}}});var oldCallbacks=[],rjsonp=/(=)\?(?=&|$)|\?\?/;jQuery.ajaxSetup({jsonp:"callback",jsonpCallback:function(){var e=oldCallbacks.pop()||jQuery.expando+"_"+nonce++;return this[e]=!0,e}}),jQuery.ajaxPrefilter("json jsonp",function(e,t,n){var r,i,s,o=e.jsonp!==!1&&(rjsonp.test(e.url)?"url":typeof e.data=="string"&&!(e.contentType||"").indexOf("application/x-www-form-urlencoded")&&rjsonp.test(e.data)&&"data");if(o||e.dataTypes[0]==="jsonp")return r=e.jsonpCallback=jQuery.isFunction(e.jsonpCallback)?e.jsonpCallback():e.jsonpCallback,o?e[o]=e[o].replace(rjsonp,"$1"+r):e.jsonp!==!1&&(e.url+=(rquery.test(e.url)?"&":"?")+e.jsonp+"="+r),e.converters["script json"]=function(){return s||jQuery.error(r+" was not called"),s[0]},e.dataTypes[0]="json",i=window[r],window[r]=function(){s=arguments},n.always(function(){window[r]=i,e[r]&&(e.jsonpCallback=t.jsonpCallback,oldCallbacks.push(r)),s&&jQuery.isFunction(i)&&i(s[0]),s=i=undefined}),"script"}),jQuery.parseHTML=function(e,t,n){if(!e||typeof e!="string")return null;typeof t=="boolean"&&(n=t,t=!1),t=t||document;var r=rsingleTag.exec(e),i=!n&&[];return r?[t.createElement(r[1])]:(r=jQuery.buildFragment([e],t,i),i&&i.length&&jQuery(i).remove(),jQuery.merge([],r.childNodes))};var _load=jQuery.fn.load;jQuery.fn.load=function(e,t,n){if(typeof e!="string"&&_load)return _load.apply(this,arguments);var r,i,s,o=this,u=e.indexOf(" ");return u>=0&&(r=jQuery.trim(e.slice(u)),e=e.slice(0,u)),jQuery.isFunction(t)?(n=t,t=undefined):t&&typeof t=="object"&&(i="POST"),o.length>0&&jQuery.ajax({url:e,type:i,dataType:"html",data:t}).done(function(e){s=arguments,o.html(r?jQuery("<div>").append(jQuery.parseHTML(e)).find(r):e)}).complete(n&&function(e,t){o.each(n,s||[e.responseText,t,e])}),this},jQuery.each(["ajaxStart","ajaxStop","ajaxComplete","ajaxError","ajaxSuccess","ajaxSend"],function(e,t){jQuery.fn[t]=function(e){return this.on(t,e)}}),jQuery.expr.filters.animated=function(e){return jQuery.grep(jQuery.timers,function(t){return e===t.elem}).length};var docElem=window.document.documentElement;jQuery.offset={setOffset:function(e,t,n){var r,i,s,o,u,a,f,l=jQuery.css(e,"position"),c=jQuery(e),h={};l==="static"&&(e.style.position="relative"),u=c.offset(),s=jQuery.css(e,"top"),a=jQuery.css(e,"left"),f=(l==="absolute"||l==="fixed")&&(s+a).indexOf("auto")>-1,f?(r=c.position(),o=r.top,i=r.left):(o=parseFloat(s)||0,i=parseFloat(a)||0),jQuery.isFunction(t)&&(t=t.call(e,n,u)),t.top!=null&&(h.top=t.top-u.top+o),t.left!=null&&(h.left=t.left-u.left+i),"using"in t?t.using.call(e,h):c.css(h)}},jQuery.fn.extend({offset:function(e){if(arguments.length)return e===undefined?this:this.each(function(t){jQuery.offset.setOffset(this,e,t)});var t,n,r=this[0],i={top:0,left:0},s=r&&r.ownerDocument;if(!s)return;return t=s.documentElement,jQuery.contains(t,r)?(typeof r.getBoundingClientRect!==strundefined&&(i=r.getBoundingClientRect()),n=getWindow(s),{top:i.top+n.pageYOffset-t.clientTop,left:i.left+n.pageXOffset-t.clientLeft}):i},position:function(){if(!this[0])return;var e,t,n=this[0],r={top:0,left:0};return jQuery.css(n,"position")==="fixed"?t=n.getBoundingClientRect():(e=this.offsetParent(),t=this.offset(),jQuery.nodeName(e[0],"html")||(r=e.offset()),r.top+=jQuery.css(e[0],"borderTopWidth",!0),r.left+=jQuery.css(e[0],"borderLeftWidth",!0)),{top:t.top-r.top-jQuery.css(n,"marginTop",!0),left:t.left-r.left-jQuery.css(n,"marginLeft",!0)}},offsetParent:function(){return this.map(function(){var e=this.offsetParent||docElem;while(e&&!jQuery.nodeName(e,"html")&&jQuery.css(e,"position")==="static")e=e.offsetParent;return e||docElem})}}),jQuery.each({scrollLeft:"pageXOffset",scrollTop:"pageYOffset"},function(e,t){var n="pageYOffset"===t;jQuery.fn[e]=function(r){return access(this,function(e,r,i){var s=getWindow(e);if(i===undefined)return s?s[t]:e[r];s?s.scrollTo(n?window.pageXOffset:i,n?i:window.pageYOffset):e[r]=i},e,r,arguments.length,null)}}),jQuery.each(["top","left"],function(e,t){jQuery.cssHooks[t]=addGetHookIf(support.pixelPosition,function(e,n){if(n)return n=curCSS(e,t),rnumnonpx.test(n)?jQuery(e).position()[t]+"px":n})}),jQuery.each({Height:"height",Width:"width"},function(e,t){jQuery.each({padding:"inner"+e,content:t,"":"outer"+e},function(n,r){jQuery.fn[r]=function(r,i){var s=arguments.length&&(n||typeof r!="boolean"),o=n||(r===!0||i===!0?"margin":"border");return access(this,function(t,n,r){var i;return jQuery.isWindow(t)?t.document.documentElement["client"+e]:t.nodeType===9?(i=t.documentElement,Math.max(t.body["scroll"+e],i["scroll"+e],t.body["offset"+e],i["offset"+e],i["client"+e])):r===undefined?jQuery.css(t,n,o):jQuery.style(t,n,r,o)},t,s?r:undefined,s,null)}})}),jQuery.fn.size=function(){return this.length},jQuery.fn.andSelf=jQuery.fn.addBack,typeof define=="function"&&define.amd&&define("jquery",[],function(){return jQuery});var _jQuery=window.jQuery,_$=window.$;return jQuery.noConflict=function(e){return window.$===jQuery&&(window.$=_$),e&&window.jQuery===jQuery&&(window.jQuery=_jQuery),jQuery},typeof noGlobal===strundefined&&(window.jQuery=window.$=jQuery),jQuery}),function(e,t){"use strict";function p(){if(n.READY)return;y.determineEventTypes(),d.each(n.gestures,function(e){w.register(e)}),y.onTouch(n.DOCUMENT,c,w.detect),y.onTouch(n.DOCUMENT,h,w.detect),n.READY=!0}var n=function(e,t){return new n.Instance(e,t||{})};n.VERSION="1.0.11",n.defaults={stop_browser_behavior:{userSelect:"none",touchAction:"pan-y",touchCallout:"none",contentZooming:"none",userDrag:"none",tapHighlightColor:"rgba(0,0,0,0)"}},n.HAS_POINTEREVENTS=e.navigator.pointerEnabled||e.navigator.msPointerEnabled,n.HAS_TOUCHEVENTS="ontouchstart"in e,n.MOBILE_REGEX=/mobile|tablet|ip(ad|hone|od)|android|silk/i,n.NO_MOUSEEVENTS=n.HAS_TOUCHEVENTS&&e.navigator.userAgent.match(n.MOBILE_REGEX),n.EVENT_TYPES={},n.UPDATE_VELOCITY_INTERVAL=16,n.DOCUMENT=e.document;var r=n.DIRECTION_DOWN="down",i=n.DIRECTION_LEFT="left",s=n.DIRECTION_UP="up",o=n.DIRECTION_RIGHT="right",u=n.POINTER_MOUSE="mouse",a=n.POINTER_TOUCH="touch",f=n.POINTER_PEN="pen",l=n.EVENT_START="start",c=n.EVENT_MOVE="move",h=n.EVENT_END="end";n.plugins=n.plugins||{},n.gestures=n.gestures||{},n.READY=!1;var d=n.utils={extend:function(n,r,i){for(var s in r){if(n[s]!==t&&i)continue;n[s]=r[s]}return n},each:function(n,r,i){var s,o;if("forEach"in n)n.forEach(r,i);else if(n.length!==t){for(s=-1;o=n[++s];)if(r.call(i,o,s,n)===!1)return}else for(s in n)if(n.hasOwnProperty(s)&&r.call(i,n[s],s,n)===!1)return},inStr:function(t,n){return t.indexOf(n)>-1},hasParent:function(t,n){while(t){if(t==n)return!0;t=t.parentNode}return!1},getCenter:function(t){var n=[],r=[],i=[],s=[],o=Math.min,u=Math.max;return t.length===1?{pageX:t[0].pageX,pageY:t[0].pageY,clientX:t[0].clientX,clientY:t[0].clientY}:(d.each(t,function(e){n.push(e.pageX),r.push(e.pageY),i.push(e.clientX),s.push(e.clientY)}),{pageX:(o.apply(Math,n)+u.apply(Math,n))/2,pageY:(o.apply(Math,r)+u.apply(Math,r))/2,clientX:(o.apply(Math,i)+u.apply(Math,i))/2,clientY:(o.apply(Math,s)+u.apply(Math,s))/2})},getVelocity:function(t,n,r){return{x:Math.abs(n/t)||0,y:Math.abs(r/t)||0}},getAngle:function(t,n){var r=n.clientX-t.clientX,i=n.clientY-t.clientY;return Math.atan2(i,r)*180/Math.PI},getDirection:function(t,n){var u=Math.abs(t.clientX-n.clientX),a=Math.abs(t.clientY-n.clientY);return u>=a?t.clientX-n.clientX>0?i:o:t.clientY-n.clientY>0?s:r},getDistance:function(t,n){var r=n.clientX-t.clientX,i=n.clientY-t.clientY;return Math.sqrt(r*r+i*i)},getScale:function(t,n){return t.length>=2&&n.length>=2?this.getDistance(n[0],n[1])/this.getDistance(t[0],t[1]):1},getRotation:function(t,n){return t.length>=2&&n.length>=2?this.getAngle(n[1],n[0])-this.getAngle(t[1],t[0]):0},isVertical:function(t){return t==s||t==r},toggleDefaultBehavior:function(t,n,r){if(!n||!t||!t.style)return;d.each(["webkit","moz","Moz","ms","o",""],function(i){d.each(n,function(e,n){i&&(n=i+n.substring(0,1).toUpperCase()+n.substring(1)),n in t.style&&(t.style[n]=!r&&e)})});var i=function(){return!1};n.userSelect=="none"&&(t.onselectstart=!r&&i),n.userDrag=="none"&&(t.ondragstart=!r&&i)}};n.Instance=function(e,t){var r=this;return p(),this.element=e,this.enabled=!0,this.options=d.extend(d.extend({},n.defaults),t||{}),this.options.stop_browser_behavior&&d.toggleDefaultBehavior(this.element,this.options.stop_browser_behavior,!1),this.eventStartHandler=y.onTouch(e,l,function(e){r.enabled&&w.startDetect(r,e)}),this.eventHandlers=[],this},n.Instance.prototype={on:function(t,n){var r=t.split(" ");return d.each(r,function(e){this.element.addEventListener(e,n,!1),this.eventHandlers.push({gesture:e,handler:n})},this),this},off:function(t,n){var r=t.split(" "),i,s;return d.each(r,function(e){this.element.removeEventListener(e,n,!1);for(i=-1;s=this.eventHandlers[++i];)s.gesture===e&&s.handler===n&&this.eventHandlers.splice(i,1)},this),this},trigger:function(t,r){r||(r={});var i=n.DOCUMENT.createEvent("Event");i.initEvent(t,!0,!0),i.gesture=r;var s=this.element;return d.hasParent(r.target,s)&&(s=r.target),s.dispatchEvent(i),this},enable:function(t){return this.enabled=t,this},dispose:function(){var t,r;this.options.stop_browser_behavior&&d.toggleDefaultBehavior(this.element,this.options.stop_browser_behavior,!0);for(t=-1;r=this.eventHandlers[++t];)this.element.removeEventListener(r.gesture,r.handler,!1);return this.eventHandlers=[],y.unbindDom(this.element,n.EVENT_TYPES[l],this.eventStartHandler),null}};var v=null,m=!1,g=!1,y=n.event={bindDom:function(e,t,n){var r=t.split(" ");d.each(r,function(t){e.addEventListener(t,n,!1)})},unbindDom:function(e,t,n){var r=t.split(" ");d.each(r,function(t){e.removeEventListener(t,n,!1)})},onTouch:function(t,r,i){var s=this,o=function(o){var u=o.type.toLowerCase();if(d.inStr(u,"mouse")&&g)return;d.inStr(u,"touch")||d.inStr(u,"pointerdown")||d.inStr(u,"mouse")&&o.which===1?m=!0:d.inStr(u,"mouse")&&!o.which&&(m=!1);if(d.inStr(u,"touch")||d.inStr(u,"pointer"))g=!0;var a=0;if(m){n.HAS_POINTEREVENTS&&r!=h?a=b.updatePointer(r,o):d.inStr(u,"touch")?a=o.touches.length:g||(a=d.inStr(u,"up")?0:1),a>0&&r==h?r=c:a||(r=h);if(a||v===null)v=o;i.call(w,s.collectEventData(t,r,s.getTouchList(v,r),o)),n.HAS_POINTEREVENTS&&r==h&&(a=b.updatePointer(r,o))}a||(v=null,m=!1,g=!1,b.reset())};return this.bindDom(t,n.EVENT_TYPES[r],o),o},determineEventTypes:function(){var t;n.HAS_POINTEREVENTS?t=b.getEvents():n.NO_MOUSEEVENTS?t=["touchstart","touchmove","touchend touchcancel"]:t=["touchstart mousedown","touchmove mousemove","touchend touchcancel mouseup"],n.EVENT_TYPES[l]=t[0],n.EVENT_TYPES[c]=t[1],n.EVENT_TYPES[h]=t[2]},getTouchList:function(t){return n.HAS_POINTEREVENTS?b.getTouchList():t.touches?t.touches:(t.identifier=1,[t])},collectEventData:function(t,n,r,i){var s=a;if(d.inStr(i.type,"mouse")||b.matchType(u,i))s=u;return{center:d.getCenter(r),timeStamp:Date.now(),target:i.target,touches:r,eventType:n,pointerType:s,srcEvent:i,preventDefault:function(){var e=this.srcEvent;e.preventManipulation&&e.preventManipulation(),e.preventDefault&&e.preventDefault()},stopPropagation:function(){this.srcEvent.stopPropagation()},stopDetect:function(){return w.stopDetect()}}}},b=n.PointerEvent={pointers:{},getTouchList:function(){var t=[];return d.each(this.pointers,function(e){t.push(e)}),t},updatePointer:function(t,n){return t==h?delete this.pointers[n.pointerId]:(n.identifier=n.pointerId,this.pointers[n.pointerId]=n),Object.keys(this.pointers).length},matchType:function(t,n){if(!n.pointerType)return!1;var r=n.pointerType,i={};return i[u]=r===u,i[a]=r===a,i[f]=r===f,i[t]},getEvents:function(){return["pointerdown MSPointerDown","pointermove MSPointerMove","pointerup pointercancel MSPointerUp MSPointerCancel"]},reset:function(){this.pointers={}}},w=n.detection={gestures:[],current:null,previous:null,stopped:!1,startDetect:function(t,n){if(this.current)return;this.stopped=!1,this.current={inst:t,startEvent:d.extend({},n),lastEvent:!1,lastVelocityEvent:!1,velocity:!1,name:""},this.detect(n)},detect:function(t){if(!this.current||this.stopped)return;t=this.extendEventData(t);var n=this.current.inst,r=n.options;return d.each(this.gestures,function(i){if(!this.stopped&&r[i.name]!==!1&&n.enabled!==!1&&i.handler.call(i,t,n)===!1)return this.stopDetect(),!1},this),this.current&&(this.current.lastEvent=t),t.eventType==h&&!t.touches.length-1&&this.stopDetect(),t},stopDetect:function(){this.previous=d.extend({},this.current),this.current=null,this.stopped=!0},getVelocityData:function(t,r,i,s){var o=this.current,u=o.lastVelocityEvent,a=o.velocity;u&&t.timeStamp-u.timeStamp>n.UPDATE_VELOCITY_INTERVAL?(a=d.getVelocity(t.timeStamp-u.timeStamp,t.center.clientX-u.center.clientX,t.center.clientY-u.center.clientY),o.lastVelocityEvent=t):o.velocity||(a=d.getVelocity(r,i,s),o.lastVelocityEvent=t),o.velocity=a,t.velocityX=a.x,t.velocityY=a.y},getInterimData:function(t){var n=this.current.lastEvent,r,i;t.eventType==h?(r=n&&n.interimAngle,i=n&&n.interimDirection):(r=n&&d.getAngle(n.center,t.center),i=n&&d.getDirection(n.center,t.center)),t.interimAngle=r,t.interimDirection=i},extendEventData:function(t){var n=this.current,r=n.startEvent;if(t.touches.length!=r.touches.length||t.touches===r.touches)r.touches=[],d.each(t.touches,function(e){r.touches.push(d.extend({},e))});var i=t.timeStamp-r.timeStamp,s=t.center.clientX-r.center.clientX,o=t.center.clientY-r.center.clientY;return this.getVelocityData(t,i,s,o),this.getInterimData(t),d.extend(t,{startEvent:r,deltaTime:i,deltaX:s,deltaY:o,distance:d.getDistance(r.center,t.center),angle:d.getAngle(r.center,t.center),direction:d.getDirection(r.center,t.center),scale:d.getScale(r.touches,t.touches),rotation:d.getRotation(r.touches,t.touches)}),t},register:function(r){var i=r.defaults||{};return i[r.name]===t&&(i[r.name]=!0),d.extend(n.defaults,i,!0),r.index=r.index||1e3,this.gestures.push(r),this.gestures.sort(function(e,t){return e.index<t.index?-1:e.index>t.index?1:0}),this.gestures}};n.gestures.Drag={name:"drag",index:50,defaults:{drag_min_distance:10,correct_for_drag_min_distance:!0,drag_max_touches:1,drag_block_horizontal:!1,drag_block_vertical:!1,drag_lock_to_axis:!1,drag_lock_min_distance:25},triggered:!1,handler:function(t,n){var u=w.current;if(u.name!=this.name&&this.triggered){n.trigger(this.name+"end",t),this.triggered=!1;return}if(n.options.drag_max_touches>0&&t.touches.length>n.options.drag_max_touches)return;switch(t.eventType){case l:this.triggered=!1;break;case c:if(t.distance<n.options.drag_min_distance&&u.name!=this.name)return;var a=u.startEvent.center;if(u.name!=this.name){u.name=this.name;if(n.options.correct_for_drag_min_distance&&t.distance>0){var f=Math.abs(n.options.drag_min_distance/t.distance);a.pageX+=t.deltaX*f,a.pageY+=t.deltaY*f,a.clientX+=t.deltaX*f,a.clientY+=t.deltaY*f,t=w.extendEventData(t)}}if(u.lastEvent.drag_locked_to_axis||n.options.drag_lock_to_axis&&n.options.drag_lock_min_distance<=t.distance)t.drag_locked_to_axis=!0;var p=u.lastEvent.direction;t.drag_locked_to_axis&&p!==t.direction&&(d.isVertical(p)?t.direction=t.deltaY<0?s:r:t.direction=t.deltaX<0?i:o),this.triggered||(n.trigger(this.name+"start",t),this.triggered=!0),n.trigger(this.name,t),n.trigger(this.name+t.direction,t);var v=d.isVertical(t.direction);(n.options.drag_block_vertical&&v||n.options.drag_block_horizontal&&!v)&&t.preventDefault();break;case h:this.triggered&&n.trigger(this.name+"end",t),this.triggered=!1}}},n.gestures.Hold={name:"hold",index:10,defaults:{hold_timeout:500,hold_threshold:2},timer:null,handler:function(t,n){switch(t.eventType){case l:clearTimeout(this.timer),w.current.name=this.name,this.timer=setTimeout(function(){w.current.name=="hold"&&n.trigger("hold",t)},n.options.hold_timeout);break;case c:t.distance>n.options.hold_threshold&&clearTimeout(this.timer);break;case h:clearTimeout(this.timer)}}},n.gestures.Release={name:"release",index:Infinity,handler:function(t,n){t.eventType==h&&n.trigger(this.name,t)}},n.gestures.Swipe={name:"swipe",index:40,defaults:{swipe_min_touches:1,swipe_max_touches:1,swipe_velocity:.7},handler:function(t,n){if(t.eventType==h){if(t.touches.length<n.options.swipe_min_touches||t.touches.length>n.options.swipe_max_touches)return;if(t.velocityX>n.options.swipe_velocity||t.velocityY>n.options.swipe_velocity)n.trigger(this.name,t),n.trigger(this.name+t.direction,t)}}},n.gestures.Tap={name:"tap",index:100,defaults:{tap_max_touchtime:250,tap_max_distance:10,tap_always:!0,doubletap_distance:20,doubletap_interval:300},has_moved:!1,handler:function(t,n){var r,i,s;if(t.eventType==l)this.has_moved=!1;else if(t.eventType==c&&!this.moved)this.has_moved=t.distance>n.options.tap_max_distance;else if(t.eventType==h&&t.srcEvent.type!="touchcancel"&&t.deltaTime<n.options.tap_max_touchtime&&!this.has_moved){r=w.previous,i=r&&r.lastEvent&&t.timeStamp-r.lastEvent.timeStamp,s=!1,r&&r.name=="tap"&&i&&i<n.options.doubletap_interval&&t.distance<n.options.doubletap_distance&&(n.trigger("doubletap",t),s=!0);if(!s||n.options.tap_always)w.current.name="tap",n.trigger(w.current.name,t)}}},n.gestures.Touch={name:"touch",index:-Infinity,defaults:{prevent_default:!1,prevent_mouseevents:!1},handler:function(t,n){if(n.options.prevent_mouseevents&&t.pointerType==u){t.stopDetect();return}n.options.prevent_default&&t.preventDefault(),t.eventType==l&&n.trigger(this.name,t)}},n.gestures.Transform={name:"transform",index:45,defaults:{transform_min_scale:.01,transform_min_rotation:1,transform_always_block:!1,transform_within_instance:!1},triggered:!1,handler:function(t,n){if(w.current.name!=this.name&&this.triggered){n.trigger(this.name+"end",t),this.triggered=!1;return}if(t.touches.length<2)return;n.options.transform_always_block&&t.preventDefault();if(n.options.transform_within_instance)for(var r=-1;t.touches[++r];)if(!d.hasParent(t.touches[r].target,n.element))return;switch(t.eventType){case l:this.triggered=!1;break;case c:var i=Math.abs(1-t.scale),s=Math.abs(t.rotation);if(i<n.options.transform_min_scale&&s<n.options.transform_min_rotation)return;w.current.name=this.name,this.triggered||(n.trigger(this.name+"start",t),this.triggered=!0),n.trigger(this.name,t),s>n.options.transform_min_rotation&&n.trigger("rotate",t),i>n.options.transform_min_scale&&(n.trigger("pinch",t),n.trigger("pinch"+(t.scale<1?"in":"out"),t));break;case h:this.triggered&&n.trigger(this.name+"end",t),this.triggered=!1}}},typeof define=="function"&&define.amd?define("hammerjs",[],function(){return n}):typeof module=="object"&&module.exports?module.exports=n:e.Hammer=n}(window);var cornerstone=function(e){"use strict";function t(t){if(t===undefined)throw"disable: element element must not be undefined";var n=e.getEnabledElements();for(var r=0;r<n.length;r++)if(n[r].element===t){var i={element:t};$(t).trigger("CornerstoneElementDisabled",i),n[r].element.removeChild(n[r].canvas),n.splice(r,1);return}}return e===undefined&&(e={}),e.disable=t,e}(cornerstone),cornerstone=function(e,t){"use strict";function n(n,r,i){if(n===undefined)throw"displayImage: parameter element cannot be undefined";if(r===undefined)throw"displayImage: parameter image cannot be undefined";var s=t.getEnabledElement(n);s.image=r,s.viewport===undefined&&(s.viewport=t.getDefaultViewport(s.canvas,r));if(i)for(var o in i)i[o]!==null&&(s.viewport[o]=i[o]);var u=new Date,a;if(s.lastImageTimeStamp!==undefined){var f=u.getTime()-s.lastImageTimeStamp;a=(1e3/f).toFixed()}s.lastImageTimeStamp=u.getTime();var l={viewport:s.viewport,element:s.element,image:s.image,enabledElement:s,frameRate:a};e(s.element).trigger("CornerstoneNewImage",l),t.updateImage(n)}return t===undefined&&(t={}),t.displayImage=n,t}($,cornerstone),cornerstone=function(e,t){"use strict";function n(e){var n=t.getEnabledElement(e);if(n.image===undefined)throw"draw: image has not been loaded yet";t.drawImage(n)}return t===undefined&&(t={}),t.draw=n,t}($,cornerstone),cornerstone=function(e,t){"use strict";function n(t,n){var r=new Date;t.image.render(t,n);var i=t.canvas.getContext("2d"),s=new Date,o=s-r,u={viewport:t.viewport,element:t.element,image:t.image,enabledElement:t,canvasContext:i,renderTimeInMs:o};e(t.element).trigger("CornerstoneImageRendered",u),t.invalid=!1}return t===undefined&&(t={}),t.drawImage=n,t}($,cornerstone),cornerstone=function(e,t){"use strict";function n(){var e=t.getEnabledElements();for(var n=0;n<e.length;n++){var r=e[n];r.invalid===!0&&t.drawImage(r)}}return t===undefined&&(t={}),t.drawInvalidated=n,t}($,cornerstone),cornerstone=function(e){"use strict";function t(t){if(t===undefined)throw"enable: parameter element cannot be undefined";var n=document.createElement("canvas");t.appendChild(n);var r={element:t,canvas:n,image:undefined,invalid:!1,data:{}};return e.addEnabledElement(r),e.resize(t,!0),t}return e===undefined&&(e={}),e.enable=t,e}(cornerstone),cornerstone=function(e){"use strict";function t(t,n){var r=e.getEnabledElement(t);return r.data.hasOwnProperty(n)===!1&&(r.data[n]={}),r.data[n]}function n(t,n){var r=e.getEnabledElement(t);delete r.data[n]}return e===undefined&&(e={}),e.getElementData=t,e.removeElementData=n,e}(cornerstone),cornerstone=function(e){"use strict";function n(e){if(e===undefined)throw"getEnabledElement: parameter element must not be undefined";for(var n=0;n<t.length;n++)if(t[n].element==e)return t[n];throw"element not enabled"}function r(e){if(e===undefined)throw"getEnabledElement: enabledElement element must not be undefined";t.push(e)}function i(e){var n=[];return t.forEach(function(t){t.image&&t.image.imageId===e&&n.push(t)}),n}function s(){return t}e===undefined&&(e={});var t=[];return e.getEnabledElement=n,e.addEnabledElement=r,e.getEnabledElementsByImageId=i,e.getEnabledElements=s,e}(cornerstone),cornerstone=function(e){"use strict";function t(t){var n=e.getEnabledElement(t),r=e.getDefaultViewport(n.canvas,n.image);n.viewport.scale=r.scale,n.viewport.translation.x=r.translation.x,n.viewport.translation.y=r.translation.y,n.viewport.rotation=r.rotation,n.viewport.hflip=r.hflip,n.viewport.vflip=r.vflip,e.updateImage(t)}return e===undefined&&(e={}),e.fitToWindow=t,e}(cornerstone),cornerstone=function(e){"use strict";function t(e,t,n,r){e.lut===undefined&&(e.lut=new Int16Array(e.maxPixelValue-Math.min(e.minPixelValue,0)+1));var i=e.lut,s=e.maxPixelValue,o=e.minPixelValue,u=e.slope,a=e.intercept,f=t,l=n,c,h,p,d,v=0;o<0&&(v=o);if(r===!0)for(d=e.minPixelValue;d<=s;d++)c=d*u+a,h=((c-l)/f+.5)*255,p=Math.min(Math.max(h,0),255),i[d+ -v]=Math.round(255-p);else for(d=e.minPixelValue;d<=s;d++)c=d*u+a,h=((c-l)/f+.5)*255,p=Math.min(Math.max(h,0),255),i[d+ -v]=Math.round(p)}return e===undefined&&(e={}),e.generateLut=t,e}(cornerstone),cornerstone=function(e){"use strict";function t(e,t){if(e===undefined)throw"getDefaultViewport: parameter canvas must not be undefined";if(t===undefined)throw"getDefaultViewport: parameter image must not be undefined";var n={scale:1,translation:{x:0,y:0},voi:{windowWidth:t.windowWidth,windowCenter:t.windowCenter},invert:t.invert,pixelReplication:!1,rotation:0,hflip:!1,vflip:!1},r=e.height/t.rows,i=e.width/t.columns;return i<r?n.scale=i:n.scale=r,n}return e===undefined&&(e={}),e.getDefaultViewport=t,e}(cornerstone),cornerstone=function(e){"use strict";function t(t,n,r,i,s){if(t===undefined)throw"getStoredPixels: parameter element must not be undefined";n=Math.round(n),r=Math.round(r);var o=e.getEnabledElement(t),u=[],a=0,f=o.image.getPixelData();for(var l=0;l<s;l++)for(var c=0;c<i;c++){var h=(l+r)*o.image.columns+(c+n);u[a++]=f[h]}return u}function n(n,r,i,s,o){var u=t(n,r,i,s,o),a=e.getEnabledElement(n),f=a.image.slope,l=a.image.intercept,c=u.map(function(e){return e*f+l});return c}return e===undefined&&(e={}),e.getStoredPixels=t,e.getPixels=n,e}(cornerstone),cornerstone=function(e){"use strict";function s(e){if(e===undefined)throw"setMaximumSizeBytes: parameter numBytes must not be undefined";if(e.toFixed===undefined)throw"setMaximumSizeBytes: parameter numBytes must be a number";r=e,o()}function o(){function e(e,t){return e.timeStamp>t.timeStamp?-1:e.timeStamp<t.timeStamp?1:0}if(i<=r)return;n.sort(e);while(i>r){var s=n[n.length-1];i-=s.sizeInBytes,delete t[s.imageId],s.imagePromise.reject(),n.pop()}}function u(e,r){if(e===undefined)throw"getImagePromise: imageId must not be undefined";if(r===undefined)throw"getImagePromise: imagePromise must not be undefined";if(t.hasOwnProperty(e)===!0)throw"putImagePromise: imageId already in cache";var s={loaded:!1,imageId:e,imagePromise:r,timeStamp:new Date,sizeInBytes:0};t[e]=s,n.push(s),r.then(function(e){s.loaded=!0;if(e.sizeInBytes===undefined)throw"putImagePromise: image does not have sizeInBytes property or";if(e.sizeInBytes.toFixed===undefined)throw"putImagePromise: image.sizeInBytes is not a number";s.sizeInBytes=e.sizeInBytes,i+=s.sizeInBytes,o()})}function a(e){if(e===undefined)throw"getImagePromise: imageId must not be undefined";var n=t[e];return n===undefined?undefined:(n.timeStamp=new Date,n.imagePromise)}function f(e){if(e===undefined)throw"removeImagePromise: imageId must not be undefined";var r=t[e];if(r===undefined)throw"removeImagePromise: imageId must not be undefined";return n.splice(n.indexOf(r),1),i-=r.sizeInBytes,delete t[e],r.imagePromise}function l(){return{maximumSizeInBytes:r,cacheSizeInBytes:i,numberOfImagesCached:n.length}}function c(){while(n.length>0){var e=n.pop();delete t[e.imageId],e.imagePromise.reject()}i=0}e===undefined&&(e={});var t={},n=[],r=1073741824,i=0;return e.imageCache={putImagePromise:u,getImagePromise:a,removeImagePromise:f,setMaximumSizeBytes:s,getCacheInfo:l,purgeCache:c},e}(cornerstone),cornerstone=function(e,t){"use strict";function i(i){var s=i.indexOf(":"),o=i.substring(0,s),u=n[o],a;return u===undefined||u===null?r!==undefined?(a=r(i),a):undefined:(a=u(i),a.then(function(n){e(t).trigger("CornerstoneImageLoaded",{image:n})}),a)}function s(e){if(e===undefined)throw"loadImage: parameter imageId must not be undefined";var n=t.imageCache.getImagePromise(e);if(n!==undefined)return n;n=i(e);if(n===undefined)throw"loadImage: no image loader for imageId";return n}function o(e){if(e===undefined)throw"loadAndCacheImage: parameter imageId must not be undefined";var n=t.imageCache.getImagePromise(e);if(n!==undefined)return n;n=i(e);if(n===undefined)throw"loadAndCacheImage: no image loader for imageId";return t.imageCache.putImagePromise(e,n),n}function u(e,t){n[e]=t}function a(e){var t=r;return r=e,t}t===undefined&&(t={});var n={},r;return t.loadImage=s,t.loadAndCacheImage=o,t.registerImageLoader=u,t.registerUnknownImageLoader=a,t}($,cornerstone),cornerstone=function(e){"use strict";function t(t){var n=e.getEnabledElement(t);n.invalid=!0;var r={element:t};$(n.element).trigger("CornerstoneInvalidated",r)}return e===undefined&&(e={}),e.invalidate=t,e}(cornerstone),cornerstone=function(e){"use strict";function t(t){var n=e.getEnabledElementsByImageId(t);n.forEach(function(t){e.drawImage(t,!0)})}return e===undefined&&(e={}),e.invalidateImageId=t,e}(cornerstone),cornerstone=function(e){"use strict";function t(t,n,r){var i=e.getEnabledElement(t);if(i.image===undefined)throw"image has not been loaded yet";var s=t.getBoundingClientRect(),o=n-s.left-window.pageXOffset,u=r-s.top-window.pageYOffset,a=o-s.width/2,f=u-s.height/2,l=i.viewport,c=i.viewport.scale,h=i.viewport.scale;i.image.rowPixelSpacing<i.image.columnPixelSpacing?c*=i.image.columnPixelSpacing/i.image.rowPixelSpacing:i.image.columnPixelSpacing<i.image.rowPixelSpacing&&(h*=i.image.rowPixelSpacing/i.image.columnPixelSpacing);var p=a/c,d=f/h,v=p-l.translation.x,m=d-l.translation.y;l.hflip&&(v*=-1),l.vflip&&(m*=-1);if(l.rotation!==0){var g=l.rotation*Math.PI/180,y=Math.cos(g),b=Math.sin(g),w=v*y-m*b,E=v*b+m*y;if(l.rotation===90||l.rotation===270||l.rotation===-90||l.rotation===-270)w*=-1,E*=-1;v=w,m=E}return v+=i.image.columns/2,m+=i.image.rows/2,{x:v,y:m}}return e===undefined&&(e={}),e.pageToPixel=t,e}(cornerstone),cornerstone=function(e){"use strict";function o(e){t.width=e.width,t.height=e.height,n=t.getContext("2d"),n.fillStyle="white",n.fillRect(0,0,t.width,t.height),r=n.getImageData(0,0,e.width,e.height)}function u(t,n){return t.lut!==undefined&&t.lut.windowCenter===n.voi.windowCenter&&t.lut.windowWidth===n.voi.windowWidth&&t.lut.invert===n.invert?t.lut:(e.generateLut(t,n.voi.windowWidth,n.voi.windowCenter,n.invert),t.lut.windowWidth=n.voi.windowWidth,t.lut.windowCenter=n.voi.windowCenter,t.lut.invert=n.invert,t.lut)}function a(e,t){return t.imageId!==i||s.windowCenter!==e.viewport.voi.windowCenter||s.windowWidth!==e.viewport.voi.windowWidth||s.invert!==e.viewport.invert||s.rotation!==e.viewport.rotation||s.hflip!==e.viewport.hflip||s.vflip!==e.viewport.vflip?!0:!1}function f(i,s,f){if(i.viewport.voi.windowWidth===i.image.windowWidth&&i.viewport.voi.windowCenter===i.image.windowCenter&&i.viewport.invert===!1)return s.getCanvas();if(a(i,s)===!1&&f!==!0)return t;(t.width!==s.width||t.height!=s.height)&&o(s);var l=u(s,i.viewport);return e.storedColorPixelDataToCanvasImageData(s,l,r.data),n.putImageData(r,0,0),t}function l(t,n){if(t===undefined)throw"drawImage: enabledElement parameter must not be undefined";var r=t.image;if(r===undefined)throw"drawImage: image must be loaded before it can be drawn";var o=t.canvas.getContext("2d");o.setTransform(1,0,0,1,0,0),o.fillStyle="black",o.fillRect(0,0,t.canvas.width,t.canvas.height),t.viewport.pixelReplication===!0?(o.imageSmoothingEnabled=!1,o.mozImageSmoothingEnabled=!1):(o.imageSmoothingEnabled=!0,o.mozImageSmoothingEnabled=!0),o.save(),e.setToPixelCoordinateSystem(t,o);var u=f(t,r,n);o.drawImage(u,0,0,r.width,r.height,0,0,r.width,r.height),o.restore(),i=r.imageId,s.windowCenter=t.viewport.voi.windowCenter,s.windowWidth=t.viewport.voi.windowWidth,s.invert=t.viewport.invert,s.rotation=t.viewport.rotation,s.hflip=t.viewport.hflip,s.vflip=t.viewport.vflip}e===undefined&&(e={});var t=document.createElement("canvas"),n,r,i,s={};return e.renderColorImage=l,e}(cornerstone),cornerstone=function(e){"use strict";function o(e){t.width=e.width,t.height=e.height,n=t.getContext("2d"),n.fillStyle="white",n.fillRect(0,0,t.width,t.height),r=n.getImageData(0,0,e.width,e.height)}function u(t,n,r){return t.lut!==undefined&&t.lut.windowCenter===n.voi.windowCenter&&t.lut.windowWidth===n.voi.windowWidth&&t.lut.invert===n.invert&&r!==!0?t.lut:(e.generateLut(t,n.voi.windowWidth,n.voi.windowCenter,n.invert),t.lut.windowWidth=n.voi.windowWidth,t.lut.windowCenter=n.voi.windowCenter,t.lut.invert=n.invert,t.lut)}function a(e,t){return t.imageId!==i||s.windowCenter!==e.viewport.voi.windowCenter||s.windowWidth!==e.viewport.voi.windowWidth||s.invert!==e.viewport.invert||s.rotation!==e.viewport.rotation||s.hflip!==e.viewport.hflip||s.vflip!==e.viewport.vflip?!0:!1}function f(i,s,f){if(a(i,s)===!1&&f!==!0)return t;(t.width!==s.width||t.height!=s.height)&&o(s);var l=u(s,i.viewport,f);return e.storedPixelDataToCanvasImageData(s,l,r.data),n.putImageData(r,0,0),t}function l(t,n){if(t===undefined)throw"drawImage: enabledElement parameter must not be undefined";var r=t.image;if(r===undefined)throw"drawImage: image must be loaded before it can be drawn";var o=t.canvas.getContext("2d");o.setTransform(1,0,0,1,0,0),o.fillStyle="black",o.fillRect(0,0,t.canvas.width,t.canvas.height),t.viewport.pixelReplication===!0?(o.imageSmoothingEnabled=!1,o.mozImageSmoothingEnabled=!1):(o.imageSmoothingEnabled=!0,o.mozImageSmoothingEnabled=!0),e.setToPixelCoordinateSystem(t,o);var u=f(t,r,n);o.drawImage(u,0,0,r.width,r.height,0,0,r.width,r.height),i=r.imageId,s.windowCenter=t.viewport.voi.windowCenter,s.windowWidth=t.viewport.voi.windowWidth,s.invert=t.viewport.invert,s.rotation=t.viewport.rotation,s.hflip=t.viewport.hflip,s.vflip=t.viewport.vflip}e===undefined&&(e={});var t=document.createElement("canvas"),n,r,i,s={};return e.renderGrayscaleImage=l,e}(cornerstone),cornerstone=function(e){"use strict";function t(t,n){if(t===undefined)throw"drawImage: enabledElement parameter must not be undefined";var r=t.image;if(r===undefined)throw"drawImage: image must be loaded before it can be drawn";var i=t.canvas.getContext("2d");i.setTransform(1,0,0,1,0,0),i.fillStyle="black",i.fillRect(0,0,t.canvas.width,t.canvas.height),t.viewport.pixelReplication===!0?(i.imageSmoothingEnabled=!1,i.mozImageSmoothingEnabled=!1):(i.imageSmoothingEnabled=!0,i.mozImageSmoothingEnabled=!0),e.setToPixelCoordinateSystem(t,i),t.viewport.voi.windowWidth===t.image.windowWidth&&t.viewport.voi.windowCenter===t.image.windowCenter&&t.viewport.invert===!1?i.drawImage(r.getImage(),0,0,r.width,r.height,0,0,r.width,r.height):e.renderColorImage(t,n)}return e===undefined&&(e={}),e.renderWebImage=t,e}(cornerstone),cornerstone=function(e){"use strict";function t(e,t){t.width=e.clientWidth,t.height=e.clientHeight,t.style.width=e.clientWidth+"px",t.style.height=e.clientHeight+"px"}function n(n,r){var i=e.getEnabledElement(n);t(n,i.canvas);if(i.image===undefined)return;r===!0?e.fitToWindow(n):e.updateImage(n)}return e===undefined&&(e={}),e.resize=n,e}(cornerstone),cornerstone=function(e){"use strict";function t(e,t,n){if(e===undefined)throw"setToPixelCoordinateSystem: parameter enabledElement must not be undefined";if(t===undefined)throw"setToPixelCoordinateSystem: parameter context must not be undefined";t.setTransform(1,0,0,1,0,0),t.translate(e.canvas.width/2,e.canvas.height/2);var r=e.viewport.scale,i=e.viewport.scale;e.image.rowPixelSpacing<e.image.columnPixelSpacing?r*=e.image.columnPixelSpacing/e.image.rowPixelSpacing:e.image.columnPixelSpacing<e.image.rowPixelSpacing&&(i*=e.image.rowPixelSpacing/e.image.columnPixelSpacing),t.scale(r,i),t.translate(e.viewport.translation.x,e.viewport.translation.y),n===undefined?n=1:t.scale(n,n);var s=e.viewport.rotation;s!==0&&t.rotate(s*Math.PI/180),e.viewport.hflip&&(t.translate(e.offsetWidth,0),t.scale(-1,1)),e.viewport.vflip&&(t.translate(0,e.offsetHeight),t.scale(1,-1)),t.translate(-e.image.width/2/n,-e.image.height/2/n)}return e===undefined&&(e={}),e.setToPixelCoordinateSystem=t,e}(cornerstone),cornerstone=function(e){"use strict";function t(e,t,n){var r=e.getPixelData(),i=e.minPixelValue,s=3,o=0,u=r.length,a=r,f=t,l=n;if(i<0)while(o<u)l[s]=f[a[o++]+ -i],s+=4;else while(o<u)l[s]=f[a[o++]],s+=4}function n(e,t,n){var r=e.minPixelValue,i=0,s=0,o=e.width*e.height*4,u=e.getPixelData(),a=t,f=n;if(r<0)while(s<o)f[i++]=a[u[s++]+ -r],f[i++]=a[u[s++]+ -r],f[i]=a[u[s]+ -r],s+=2,i+=2;else while(s<o)f[i++]=a[u[s++]],f[i++]=a[u[s++]],f[i]=a[u[s]],s+=2,i+=2}return e===undefined&&(e={}),e.storedPixelDataToCanvasImageData=t,e.storedColorPixelDataToCanvasImageData=n,e}(cornerstone),cornerstone=function(e){"use strict";function t(t,n){var r=e.getEnabledElement(t);if(r.image===undefined)throw"updateImage: image has not been loaded yet";e.drawImage(r,n)}return e===undefined&&(e={}),e.updateImage=t,e}(cornerstone),cornerstone=function(e){"use strict";function t(t,n){var r=e.getEnabledElement(t);r.viewport.scale=n.scale,r.viewport.translation.x=n.translation.x,r.viewport.translation.y=n.translation.y,r.viewport.voi.windowWidth=n.voi.windowWidth,r.viewport.voi.windowCenter=n.voi.windowCenter,r.viewport.invert=n.invert,r.viewport.pixelReplication=n.pixelReplication,r.viewport.rotation=n.rotation,r.viewport.hflip=n.hflip,r.viewport.vflip=n.vflip,r.viewport.voi.windowWidth<1&&(r.viewport.voi.windowWidth=1),r.viewport.scale<1e-4&&(r.viewport.scale=.25);if(r.viewport.rotation===360||r.viewport.rotation===-360)r.viewport.rotation=0;e.updateImage(t)}function n(t){var n=e.getEnabledElement(t),r=n.viewport;return r===undefined?undefined:{scale:r.scale,translation:{x:r.translation.x,y:r.translation.y},voi:{windowWidth:r.voi.windowWidth,windowCenter:r.voi.windowCenter},invert:r.invert,pixelReplication:r.pixelReplication,rotation:r.rotation,hflip:r.hflip,vflip:r.vflip}}return e===undefined&&(e={}),e.getViewport=n,e.setViewport=t,e}(cornerstone);define("cornerstone",function(){});var cornerstoneMath=function(e){"use strict";function t(e){return e*e}function n(e,n){return t(e.x-n.x)+t(e.y-n.y)}function r(e,t){var r=n(e.start,e.end);if(r===0)return n(t,e.start);var i=((t.x-e.start.x)*(e.end.x-e.start.x)+(t.y-e.start.y)*(e.end.y-e.start.y))/r;if(i<0)return n(t,e.start);if(i>1)return n(t,e.end);var s={x:e.start.x+i*(e.end.x-e.start.x),y:e.start.y+i*(e.end.y-e.start.y)};return n(t,s)}function i(e,t){return Math.sqrt(r(e,t))}return e===undefined&&(e={}),e.lineSegment={distanceToPoint:i},e}(cornerstoneMath),cornerstoneMath=function(e){"use strict";function t(e,t,n){return e<t?t:e>n?n:e}function n(e){var t=Math.PI/180;return e*t}function r(e){var t=180/Math.PI;return e*t}return e===undefined&&(e={}),e.clamp=t,e.degToRad=n,e.radToDeg=r,e}(cornerstoneMath),cornerstoneMath=function(e){"use strict";return e===undefined&&(e={}),e.Matrix4=function(t,n,r,i,s,o,u,a,f,l,c,h,p,d,v,m){this.elements=new Float32Array(16);var g=this.elements;g[0]=t!==undefined?t:1,g[4]=n||0,g[8]=r||0,g[12]=i||0,g[1]=s||0,g[5]=o!==undefined?o:1,g[9]=u||0,g[13]=a||0,g[2]=f||0,g[6]=l||0,g[10]=c!==undefined?c:1,g[14]=h||0,g[3]=p||0,g[7]=d||0,g[11]=v||0,g[15]=m!==undefined?m:1},e.Matrix4.prototype.makeRotationFromQuaternion=function(e){var t=this.elements,n=e.x,r=e.y,i=e.z,s=e.w,o=n+n,u=r+r,a=i+i,f=n*o,l=n*u,c=n*a,h=r*u,p=r*a,d=i*a,v=s*o,m=s*u,g=s*a;return t[0]=1-(h+d),t[4]=l-g,t[8]=c+m,t[1]=l+g,t[5]=1-(f+d),t[9]=p-v,t[2]=c-m,t[6]=p+v,t[10]=1-(f+h),t[3]=0,t[7]=0,t[11]=0,t[12]=0,t[13]=0,t[14]=0,t[15]=1,this},e.Matrix4.prototype.multiplyMatrices=function(e,t){var n=e.elements,r=t.elements,i=this.elements,s=n[0],o=n[4],u=n[8],a=n[12],f=n[1],l=n[5],c=n[9],h=n[13],p=n[2],d=n[6],v=n[10],m=n[14],g=n[3],y=n[7],b=n[11],w=n[15],E=r[0],S=r[4],x=r[8],T=r[12],N=r[1],C=r[5],k=r[9],L=r[13],A=r[2],O=r[6],M=r[10],_=r[14],D=r[3],P=r[7],H=r[11],B=r[15];return i[0]=s*E+o*N+u*A+a*D,i[4]=s*S+o*C+u*O+a*P,i[8]=s*x+o*k+u*M+a*H,i[12]=s*T+o*L+u*_+a*B,i[1]=f*E+l*N+c*A+h*D,i[5]=f*S+l*C+c*O+h*P,i[9]=f*x+l*k+c*M+h*H,i[13]=f*T+l*L+c*_+h*B,i[2]=p*E+d*N+v*A+m*D,i[6]=p*S+d*C+v*O+m*P,i[10]=p*x+d*k+v*M+m*H,i[14]=p*T+d*L+v*_+m*B,i[3]=g*E+y*N+b*A+w*D,i[7]=g*S+y*C+b*O+w*P,i[11]=g*x+y*k+b*M+w*H,i[15]=g*T+y*L+b*_+w*B,this},e.Matrix4.prototype.multiply=function(e,t){return t!==undefined?(console.warn("DEPRECATED: Matrix4's .multiply() now only accepts one argument. Use .multiplyMatrices( a, b ) instead."),this.multiplyMatrices(e,t)):this.multiplyMatrices(this,e)},e.Matrix4.prototype.getInverse=function(e,t){var n=this.elements,r=e.elements,i=r[0],s=r[4],o=r[8],u=r[12],a=r[1],f=r[5],l=r[9],c=r[13],h=r[2],p=r[6],d=r[10],v=r[14],m=r[3],g=r[7],y=r[11],b=r[15];n[0]=l*v*g-c*d*g+c*p*y-f*v*y-l*p*b+f*d*b,n[4]=u*d*g-o*v*g-u*p*y+s*v*y+o*p*b-s*d*b,n[8]=o*c*g-u*l*g+u*f*y-s*c*y-o*f*b+s*l*b,n[12]=u*l*p-o*c*p-u*f*d+s*c*d+o*f*v-s*l*v,n[1]=c*d*m-l*v*m-c*h*y+a*v*y+l*h*b-a*d*b,n[5]=o*v*m-u*d*m+u*h*y-i*v*y-o*h*b+i*d*b,n[9]=u*l*m-o*c*m-u*a*y+i*c*y+o*a*b-i*l*b,n[13]=o*c*h-u*l*h+u*a*d-i*c*d-o*a*v+i*l*v,n[2]=f*v*m-c*p*m+c*h*g-a*v*g-f*h*b+a*p*b,n[6]=u*p*m-s*v*m-u*h*g+i*v*g+s*h*b-i*p*b,n[10]=s*c*m-u*f*m+u*a*g-i*c*g-s*a*b+i*f*b,n[14]=u*f*h-s*c*h-u*a*p+i*c*p+s*a*v-i*f*v,n[3]=l*p*m-f*d*m-l*h*g+a*d*g+f*h*y-a*p*y,n[7]=s*d*m-o*p*m+o*h*g-i*d*g-s*h*y+i*p*y,n[11]=o*f*m-s*l*m-o*a*g+i*l*g+s*a*y-i*f*y,n[15]=s*l*h-o*f*h+o*a*p-i*l*p-s*a*d+i*f*d;var w=i*n[0]+a*n[4]+h*n[8]+m*n[12];if(w===0){var E="Matrix4.getInverse(): can't invert matrix, determinant is 0";if(t||!1)throw new Error(E);return console.warn(E),this.identity(),this}return this.multiplyScalar(1/w),this},e.Matrix4.prototype.applyToVector3Array=function(){var t=new e.Vector3;return function(e,n,r){n===undefined&&(n=0),r===undefined&&(r=e.length);for(var i=0,s=n,o;i<r;i+=3,s+=3)t.x=e[s],t.y=e[s+1],t.z=e[s+2],t.applyMatrix4(this),e[s]=t.x,e[s+1]=t.y,e[s+2]=t.z;return e}},e.Matrix4.prototype.makeTranslation=function(e,t,n){return this.set(1,0,0,e,0,1,0,t,0,0,1,n,0,0,0,1),this},e.Matrix4.prototype.multiplyScalar=function(e){var t=this.elements;return t[0]*=e,t[4]*=e,t[8]*=e,t[12]*=e,t[1]*=e,t[5]*=e,t[9]*=e,t[13]*=e,t[2]*=e,t[6]*=e,t[10]*=e,t[14]*=e,t[3]*=e,t[7]*=e,t[11]*=e,t[15]*=e,this},e.Matrix4.prototype.set=function(e,t,n,r,i,s,o,u,a,f,l,c,h,p,d,v){var m=this.elements;return m[0]=e,m[4]=t,m[8]=n,m[12]=r,m[1]=i,m[5]=s,m[9]=o,m[13]=u,m[2]=a,m[6]=f,m[10]=l,m[14]=c,m[3]=h,m[7]=p,m[11]=d,m[15]=v,this},e.Matrix4.prototype.makeScale=function(e,t,n){return this.set(e,0,0,0,0,t,0,0,0,0,n,0,0,0,0,1),this},e}(cornerstoneMath),cornerstoneMath=function(e){"use strict";function t(e){return{x:e.pageX,y:e.pageY}}function n(e,t){return{x:e.x-t.x,y:e.y-t.y}}function r(e){return{x:e.x,y:e.y}}function i(e,t){return Math.sqrt(s(e,t))}function s(e,t){var r=n(e,t);return r.x*r.x+r.y*r.y}function o(e,t){return e.x<t.left||e.x>t.left+t.width||e.y<t.top||e.y>t.top+t.height?!1:!0}return e===undefined&&(e={}),e.point={subtract:n,copy:r,pageToPoint:t,distance:i,distanceSquared:s,insideRect:o},e}(cornerstoneMath),cornerstoneMath=function(e){"use strict";return e===undefined&&(e={}),e.Quaternion=function(t,n,r,i){this.x=t||0,this.y=n||0,this.z=r||0,this.w=i!==undefined?i:1},e.Quaternion.prototype.setFromAxisAngle=function(e,t){var n=t/2,r=Math.sin(n);return this.x=e.x*r,this.y=e.y*r,this.z=e.z*r,this.w=Math.cos(n),this},e.Quaternion.prototype.multiplyQuaternions=function(e,t){var n=e.x,r=e.y,i=e.z,s=e.w,o=t.x,u=t.y,a=t.z,f=t.w;return this.x=n*f+s*o+r*a-i*u,this.y=r*f+s*u+i*o-n*a,this.z=i*f+s*a+n*u-r*o,this.w=s*f-n*o-r*u-i*a,this},e.Quaternion.prototype.setFromRotationMatrix=function(e){var t=e.elements,n=t[0],r=t[4],i=t[8],s=t[1],o=t[5],u=t[9],a=t[2],f=t[6],l=t[10],c=n+o+l,h;return c>0?(h=.5/Math.sqrt(c+1),this.w=.25/h,this.x=(f-u)*h,this.y=(i-a)*h,this.z=(s-r)*h):n>o&&n>l?(h=2*Math.sqrt(1+n-o-l),this.w=(f-u)/h,this.x=.25*h,this.y=(r+s)/h,this.z=(i+a)/h):o>l?(h=2*Math.sqrt(1+o-n-l),this.w=(i-a)/h,this.x=(r+s)/h,this.y=.25*h,this.z=(u+f)/h):(h=2*Math.sqrt(1+l-n-o),this.w=(s-r)/h,this.x=(i+a)/h,this.y=(u+f)/h,this.z=.25*h),this},e}(cornerstoneMath),cornerstoneMath=function(e){"use strict";function t(e){var t={start:{x:e.left,y:e.top},end:{x:e.left+e.width,y:e.top}},n={start:{x:e.left+e.width,y:e.top},end:{x:e.left+e.width,y:e.top+e.height}},r={start:{x:e.left+e.width,y:e.top+e.height},end:{x:e.left,y:e.top+e.height}},i={start:{x:e.left,y:e.top+e.height},end:{x:e.left,y:e.top}},s=[t,n,r,i];return s}function n(t,n,r){r===undefined&&(r=5);var i=e.lineSegment.distanceToPoint(n,t);return i<r}function r(n,r){var i=655535,s=t(n);return s.forEach(function(t){var n=e.lineSegment.distanceToPoint(t,r);n<i&&(i=n)}),i}return e===undefined&&(e={}),e.rect={distanceToPoint:r},e}(cornerstoneMath),cornerstoneMath=function(e){"use strict";return e===undefined&&(e={}),e.Vector3=function(e,t,n){this.x=e||0,this.y=t||0,this.z=n||0},e.Vector3.prototype={constructor:e.Vector3,set:function(e,t,n){return this.x=e,this.y=t,this.z=n,this},setX:function(e){return this.x=e,this},setY:function(e){return this.y=e,this},setZ:function(e){return this.z=e,this},setComponent:function(e,t){switch(e){case 0:this.x=t;break;case 1:this.y=t;break;case 2:this.z=t;break;default:throw new Error("index is out of range: "+e)}},getComponent:function(e){switch(e){case 0:return this.x;case 1:return this.y;case 2:return this.z;default:throw new Error("index is out of range: "+e)}},copy:function(e){return this.x=e.x,this.y=e.y,this.z=e.z,this},add:function(e,t){return t!==undefined?(console.warn("DEPRECATED: Vector3's .add() now only accepts one argument. Use .addVectors( a, b ) instead."),this.addVectors(e,t)):(this.x+=e.x,this.y+=e.y,this.z+=e.z,this)},addScalar:function(e){return this.x+=e,this.y+=e,this.z+=e,this},addVectors:function(e,t){return this.x=e.x+t.x,this.y=e.y+t.y,this.z=e.z+t.z,this},sub:function(e,t){return t!==undefined?(console.warn("DEPRECATED: Vector3's .sub() now only accepts one argument. Use .subVectors( a, b ) instead."),this.subVectors(e,t)):(this.x-=e.x,this.y-=e.y,this.z-=e.z,this)},subVectors:function(e,t){return this.x=e.x-t.x,this.y=e.y-t.y,this.z=e.z-t.z,this},multiply:function(e,t){return t!==undefined?(console.warn("DEPRECATED: Vector3's .multiply() now only accepts one argument. Use .multiplyVectors( a, b ) instead."),this.multiplyVectors(e,t)):(this.x*=e.x,this.y*=e.y,this.z*=e.z,this)},multiplyScalar:function(e){return this.x*=e,this.y*=e,this.z*=e,this},multiplyVectors:function(e,t){return this.x=e.x*t.x,this.y=e.y*t.y,this.z=e.z*t.z,this},applyAxisAngle:function(){var t;return function(n,r){return t===undefined&&(t=new e.Quaternion),this.applyQuaternion(t.setFromAxisAngle(n,r)),this}}(),applyMatrix3:function(e){var t=this.x,n=this.y,r=this.z,i=e.elements;return this.x=i[0]*t+i[3]*n+i[6]*r,this.y=i[1]*t+i[4]*n+i[7]*r,this.z=i[2]*t+i[5]*n+i[8]*r,this},applyMatrix4:function(e){var t=this.x,n=this.y,r=this.z,i=e.elements;return this.x=i[0]*t+i[4]*n+i[8]*r+i[12],this.y=i[1]*t+i[5]*n+i[9]*r+i[13],this.z=i[2]*t+i[6]*n+i[10]*r+i[14],this},applyProjection:function(e){var t=this.x,n=this.y,r=this.z,i=e.elements,s=1/(i[3]*t+i[7]*n+i[11]*r+i[15]);return this.x=(i[0]*t+i[4]*n+i[8]*r+i[12])*s,this.y=(i[1]*t+i[5]*n+i[9]*r+i[13])*s,this.z=(i[2]*t+i[6]*n+i[10]*r+i[14])*s,this},applyQuaternion:function(e){var t=this.x,n=this.y,r=this.z,i=e.x,s=e.y,o=e.z,u=e.w,a=u*t+s*r-o*n,f=u*n+o*t-i*r,l=u*r+i*n-s*t,c=-i*t-s*n-o*r;return this.x=a*u+c*-i+f*-o-l*-s,this.y=f*u+c*-s+l*-i-a*-o,this.z=l*u+c*-o+a*-s-f*-i,this},transformDirection:function(e){var t=this.x,n=this.y,r=this.z,i=e.elements;return this.x=i[0]*t+i[4]*n+i[8]*r,this.y=i[1]*t+i[5]*n+i[9]*r,this.z=i[2]*t+i[6]*n+i[10]*r,this.normalize(),this},divide:function(e){return this.x/=e.x,this.y/=e.y,this.z/=e.z,this},divideScalar:function(e){if(e!==0){var t=1/e;this.x*=t,this.y*=t,this.z*=t}else this.x=0,this.y=0,this.z=0;return this},min:function(e){return this.x>e.x&&(this.x=e.x),this.y>e.y&&(this.y=e.y),this.z>e.z&&(this.z=e.z),this},max:function(e){return this.x<e.x&&(this.x=e.x),this.y<e.y&&(this.y=e.y),this.z<e.z&&(this.z=e.z),this},clamp:function(e,t){return this.x<e.x?this.x=e.x:this.x>t.x&&(this.x=t.x),this.y<e.y?this.y=e.y:this.y>t.y&&(this.y=t.y),this.z<e.z?this.z=e.z:this.z>t.z&&(this.z=t.z),this},clampScalar:function(){var t,n;return function(r,i){return t===undefined&&(t=new e.Vector3,n=new e.Vector3),t.set(r,r,r),n.set(i,i,i),this.clamp(t,n)}}(),floor:function(){return this.x=Math.floor(this.x),this.y=Math.floor(this.y),this.z=Math.floor(this.z),this},ceil:function(){return this.x=Math.ceil(this.x),this.y=Math.ceil(this.y),this.z=Math.ceil(this.z),this},round:function(){return this.x=Math.round(this.x),this.y=Math.round(this.y),this.z=Math.round(this.z),this},roundToZero:function(){return this.x=this.x<0?Math.ceil(this.x):Math.floor(this.x),this.y=this.y<0?Math.ceil(this.y):Math.floor(this.y),this.z=this.z<0?Math.ceil(this.z):Math.floor(this.z),this},negate:function(){return this.multiplyScalar(-1)},dot:function(e){return this.x*e.x+this.y*e.y+this.z*e.z},lengthSq:function(){return this.x*this.x+this.y*this.y+this.z*this.z},length:function(){return Math.sqrt(this.x*this.x+this.y*this.y+this.z*this.z)},lengthManhattan:function(){return Math.abs(this.x)+Math.abs(this.y)+Math.abs(this.z)},normalize:function(){return this.divideScalar(this.length())},setLength:function(e){var t=this.length();return t!==0&&e!==t&&this.multiplyScalar(e/t),this},lerp:function(e,t){return this.x+=(e.x-this.x)*t,this.y+=(e.y-this.y)*t,this.z+=(e.z-this.z)*t,this},cross:function(e,t){if(t!==undefined)return console.warn("DEPRECATED: Vector3's .cross() now only accepts one argument. Use .crossVectors( a, b ) instead."),this.crossVectors(e,t);var n=this.x,r=this.y,i=this.z;return this.x=r*e.z-i*e.y,this.y=i*e.x-n*e.z,this.z=n*e.y-r*e.x,this},crossVectors:function(e,t){var n=e.x,r=e.y,i=e.z,s=t.x,o=t.y,u=t.z;return this.x=r*u-i*o,this.y=i*s-n*u,this.z=n*o-r*s,this},projectOnVector:function(){var t,n;return function(r){return t===undefined&&(t=new e.Vector3),t.copy(r).normalize(),n=this.dot(t),this.copy(t).multiplyScalar(n)}}(),projectOnPlane:function(){var t;return function(n){return t===undefined&&(t=new e.Vector3),t.copy(this).projectOnVector(n),this.sub(t)}}(),reflect:function(){var t;return function(n){return t===undefined&&(t=new e.Vector3),this.sub(t.copy(n).multiplyScalar(2*this.dot(n)))}}(),angleTo:function(t){var n=this.dot(t)/(this.length()*t.length());return Math.acos(e.clamp(n,-1,1))},distanceTo:function(e){return Math.sqrt(this.distanceToSquared(e))},distanceToSquared:function(e){var t=this.x-e.x,n=this.y-e.y,r=this.z-e.z;return t*t+n*n+r*r},setEulerFromRotationMatrix:function(e,t){console.error("REMOVED: Vector3's setEulerFromRotationMatrix has been removed in favor of Euler.setFromRotationMatrix(), please update your code.")},setEulerFromQuaternion:function(e,t){console.error("REMOVED: Vector3's setEulerFromQuaternion: has been removed in favor of Euler.setFromQuaternion(), please update your code.")},getPositionFromMatrix:function(e){return console.warn("DEPRECATED: Vector3's .getPositionFromMatrix() has been renamed to .setFromMatrixPosition(). Please update your code."),this.setFromMatrixPosition(e)},getScaleFromMatrix:function(e){return console.warn("DEPRECATED: Vector3's .getScaleFromMatrix() has been renamed to .setFromMatrixScale(). Please update your code."),this.setFromMatrixScale(e)},getColumnFromMatrix:function(e,t){return console.warn("DEPRECATED: Vector3's .getColumnFromMatrix() has been renamed to .setFromMatrixColumn(). Please update your code."),this.setFromMatrixColumn(e,t)},setFromMatrixPosition:function(e){return this.x=e.elements[12],this.y=e.elements[13],this.z=e.elements[14],this},setFromMatrixScale:function(e){var t=this.set(e.elements[0],e.elements[1],e.elements[2]).length(),n=this.set(e.elements[4],e.elements[5],e.elements[6]).length(),r=this.set(e.elements[8],e.elements[9],e.elements[10]).length();return this.x=t,this.y=n,this.z=r,this},setFromMatrixColumn:function(e,t){var n=e*4,r=t.elements;return this.x=r[n],this.y=r[n+1],this.z=r[n+2],this},equals:function(e){return e.x===this.x&&e.y===this.y&&e.z===this.z},fromArray:function(e){return this.x=e[0],this.y=e[1],this.z=e[2],this},toArray:function(){return[this.x,this.y,this.z]},clone:function(){return new e.Vector3(this.x,this.y,this.z)}},e}(cornerstoneMath);define("cornerstoneMath",function(){});var cornerstoneTools=function(e,t,n){"use strict";function r(n){if(n.originalEvent.type==="mousewheel"&&n.originalEvent.wheelDeltaY===0)return;if(n.originalEvent.type==="DOMMouseScroll"&&n.originalEvent.axis===1)return;var r=n.currentTarget,i=t.pageToPixel(r,n.pageX,n.pageY);n=window.event||n;var s=n.wheelDelta||-n.detail||-n.originalEvent.detail,o=Math.max(-1,Math.min(1,s)),u={element:r,viewport:t.getViewport(r),image:t.getEnabledElement(r).image,direction:o,pageX:n.pageX,pageY:n.pageY,imageX:i.x,imageY:i.y};e(r).trigger("CornerstoneToolsMouseWheel",u)}function s(t){e(t).on(i,r)}function o(t){e(t).unbind(i,r)}n===undefined&&(n={});var i="mousewheel DOMMouseScroll";return n.mouseWheelInput={enable:s,disable:o},n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n,r){"use strict";function i(t){e(t.element).trigger("CornerstoneToolsMouseDownActivate",t)}function s(s){function p(i){var s={page:n.point.pageToPoint(i),image:t.pageToPixel(u,i.pageX,i.pageY)},o={page:n.point.subtract(s.page,f.page),image:n.point.subtract(s.image,f.image)},c={which:h,viewport:t.getViewport(u),image:t.getEnabledElement(u).image,element:u,startPoints:a,lastPoints:f,currentPoints:s,deltaPoints:o};return e(l.element).trigger("CornerstoneToolsMouseDrag",c),f=r.copyPoints(s),r.pauseEvent(i)}function d(r){var i={page:n.point.pageToPoint(r),image:t.pageToPixel(u,r.pageX,r.pageY)},s={page:n.point.subtract(i.page,f.page),image:n.point.subtract(i.image,f.image)},o={event:r,which:h,viewport:t.getViewport(u),image:t.getEnabledElement(u).image,element:u,startPoints:a,lastPoints:f,currentPoints:i,deltaPoints:s},c=jQuery.Event("CornerstoneToolsMouseUp",o);e(l.element).trigger(c,o),e(document).off("mousemove",p),e(document).off("mouseup",d)}var o=s.data,u=s.currentTarget,a={page:n.point.pageToPoint(s),image:t.pageToPixel(u,s.pageX,s.pageY)},f=r.copyPoints(a),l={event:s,which:s.which,viewport:t.getViewport(u),image:t.getEnabledElement(u).image,element:u,startPoints:a,lastPoints:f,currentPoints:a,deltaPoints:{x:0,y:0}},c=jQuery.Event("CornerstoneToolsMouseDown",l);e(l.element).trigger(c,l);if(c.isImmediatePropagationStopped()===!1&&i(l)===!0)return r.pauseEvent(s);var h=s.which;return e(document).on("mousemove",p),e(document).on("mouseup",d),r.pauseEvent(s)}function o(i){var s=i.data,o=i.currentTarget,u={page:n.point.pageToPoint(i),image:t.pageToPixel(o,i.pageX,i.pageY)},a=r.copyPoints(u),f=i.which,l={page:n.point.pageToPoint(i),image:t.pageToPixel(o,i.pageX,i.pageY)},c={page:n.point.subtract(l.page,a.page),image:n.point.subtract(l.image,a.image)},h={which:f,viewport:t.getViewport(o),image:t.getEnabledElement(o).image,element:o,startPoints:u,lastPoints:a,currentPoints:l,deltaPoints:c};e(o).trigger("CornerstoneToolsMouseMove",h),a=r.copyPoints(l)}function u(t){e(t).on("mousedown",s),e(t).on("mousemove",o)}function a(t){e(t).off("mousedown",s),e(t).off("mousemove",o)}return r===undefined&&(r={}),r.mouseInput={enable:u,disable:a},r}($,cornerstone,cornerstoneMath,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function r(t){var n={activate:function(n,r,i){e(n).off("CornerstoneToolsMouseDownActivate",t);var s={mouseButtonMask:r,options:i};e(n).on("CornerstoneToolsMouseDownActivate",s,t)},disable:function(n){e(n).off("CornerstoneToolsMouseDownActivate",t)},enable:function(n){e(n).off("CornerstoneToolsMouseDownActivate",t)},deactivate:function(n){e(n).off("CornerstoneToolsMouseDownActivate",t)}};return n}return n===undefined&&(n={}),n.simpleMouseButtonTool=r,n}($,cornerstone,cornerstoneTools),coordsData,cornerstoneTools=function(e,t,n,r){"use strict";function i(i){function s(t){var n=i.createNewMeasurement(t);r.addToolState(t.element,i.toolType,n),e(t.element).off("CornerstoneToolsMouseMove",u),r.moveHandle(t,n.handles.end,function(){r.anyHandlesOutsideImage(t,n.handles)&&r.removeToolState(t.element,i.toolType,n),e(t.element).on("CornerstoneToolsMouseMove",u)})}function o(e,t){if(r.isMouseButtonEnabled(t.which,e.data.mouseButtonMask))return s(t),!1}function u(e,n){r.activeToolcoordinate.setCoords(n);if(n.which!==0)return;var s=r.getToolState(n.element,i.toolType);if(s===undefined)return;var o=!1;for(var u=0;u<s.data.length;u++){var a=s.data[u];r.handleActivator(a.handles,n.currentPoints.image,n.viewport.scale)===!0&&(o=!0)}o===!0&&t.updateImage(n.element)}function a(e,t){for(var r in e.handles){var i=n.point.distanceSquared(e.handles[r],t);if(i<25)return e.handles[r]}}function f(t,n){function o(){r.anyHandlesOutsideImage(n,s.handles)&&r.removeToolState(n.element,i.toolType,s),e(n.element).on("CornerstoneToolsMouseMove",u)}var s;if(r.isMouseButtonEnabled(n.which,t.data.mouseButtonMask)){var f=n.startPoints.image,l=r.getToolState(t.currentTarget,i.toolType),c;if(l!==undefined)for(c=0;c<l.data.length;c++){s=l.data[c];var h=a(s,f);if(h!==undefined)return e(n.element).off("CornerstoneToolsMouseMove",u),r.moveHandle(n,h,o),t.stopImmediatePropagation(),!1}if(l!==undefined&&i.pointNearTool!==undefined)for(c=0;c<l.data.length;c++){s=l.data[c];if(i.pointNearTool(s,f))return e(n.element).off("CornerstoneToolsMouseMove",u),r.moveAllHandles(t,s,l,!0),t.stopImmediatePropagation(),!1}}}function l(n){e(n).off("CornerstoneImageRendered",i.onImageRendered),e(n).off("CornerstoneToolsMouseMove",u),e(n).off("CornerstoneToolsMouseDown",f),e(n).off("CornerstoneToolsMouseDownActivate",o),t.updateImage(n)}function c(n){e(n).off("CornerstoneImageRendered",i.onImageRendered),e(n).off("CornerstoneToolsMouseMove",u),e(n).off("CornerstoneToolsMouseDown",f),e(n).off("CornerstoneToolsMouseDownActivate",o),e(n).on("CornerstoneImageRendered",i.onImageRendered),t.updateImage(n)}function h(n,r){var s={mouseButtonMask:r};e(n).off("CornerstoneImageRendered",i.onImageRendered),e(n).off("CornerstoneToolsMouseMove",u),e(n).off("CornerstoneToolsMouseDown",f),e(n).off("CornerstoneToolsMouseDownActivate",o),e(n).on("CornerstoneImageRendered",i.onImageRendered),e(n).on("CornerstoneToolsMouseMove",s,u),e(n).on("CornerstoneToolsMouseDown",s,f),e(n).on("CornerstoneToolsMouseDownActivate",s,o),t.updateImage(n)}function p(n,r){var s={mouseButtonMask:r};e(n).off("CornerstoneImageRendered",i.onImageRendered),e(n).off("CornerstoneToolsMouseMove",u),e(n).off("CornerstoneToolsMouseDown",f),e(n).off("CornerstoneToolsMouseDownActivate",o),e(n).on("CornerstoneImageRendered",i.onImageRendered),e(n).on("CornerstoneToolsMouseMove",s,u),e(n).on("CornerstoneToolsMouseDown",s,f),t.updateImage(n)}var d={enable:c,disable:l,activate:h,deactivate:p};return d}return r===undefined&&(r={}),r.mouseButtonTool=i,r}($,cornerstone,cornerstoneMath,cornerstoneTools),coordsData,cornerstoneTools=function(e,t,n,r){"use strict";function i(i,s){function o(t){var n=i.createNewMeasurement(t);r.addToolState(t.element,i.toolType,n),e(t.element).off("CornerstoneToolsMouseMove",a),r.moveHandle(t,n.handles.end,function(){r.anyHandlesOutsideImage(t,n.handles)&&r.removeToolState(t.element,i.toolType,n),e(t.element).on("CornerstoneToolsMouseMove",a)},s)}function u(e,t){if(r.isMouseButtonEnabled(t.which,e.data.mouseButtonMask))return o(t),!1}function a(e,n){r.activeToolcoordinate.setCoords(n);if(n.which!==0)return;var s=r.getToolState(n.element,i.toolType);if(s===undefined)return;var o=!1;for(var u=0;u<s.data.length;u++){var a=s.data[u];r.handleActivator(a.handles,n.currentPoints.image,n.viewport.scale)===!0&&(o=!0)}o===!0&&t.updateImage(n.element)}function f(e,t){for(var r in e.handles){var i=n.point.distanceSquared(e.handles[r],t);if(i<25)return e.handles[r]}}function l(t,n){function u(){r.anyHandlesOutsideImage(n,o.handles)&&r.removeToolState(n.element,i.toolType,o),e(n.element).on("CornerstoneToolsMouseMove",a)}var o;if(r.isMouseButtonEnabled(n.which,t.data.mouseButtonMask)){var l=n.startPoints.image,c=r.getToolState(t.currentTarget,i.toolType),h;if(c!==undefined)for(h=0;h<c.data.length;h++){o=c.data[h];var p=f(o,l);if(p!==undefined)return e(n.element).off("CornerstoneToolsMouseMove",a),r.moveHandle(n,p,u,s),t.stopImmediatePropagation(),!1}if(c!==undefined&&i.pointInsideRect!==undefined)for(h=0;h<c.data.length;h++){o=c.data[h];if(i.pointInsideRect(o,l))return e(n.element).off("CornerstoneToolsMouseMove",a),r.moveAllHandles(t,o,c,!1,s),t.stopImmediatePropagation(),!1}}}function c(n){e(n).off("CornerstoneImageRendered",i.onImageRendered),e(n).off("CornerstoneToolsMouseMove",a),e(n).off("CornerstoneToolsMouseDown",l),e(n).off("CornerstoneToolsMouseDownActivate",u),t.updateImage(n)}function h(n){e(n).off("CornerstoneImageRendered",i.onImageRendered),e(n).off("CornerstoneToolsMouseMove",a),e(n).off("CornerstoneToolsMouseDown",l),e(n).off("CornerstoneToolsMouseDownActivate",u),e(n).on("CornerstoneImageRendered",i.onImageRendered),t.updateImage(n)}function p(n,r){var s={mouseButtonMask:r};e(n).off("CornerstoneImageRendered",i.onImageRendered),e(n).off("CornerstoneToolsMouseMove",a),e(n).off("CornerstoneToolsMouseDown",l),e(n).off("CornerstoneToolsMouseDownActivate",u),e(n).on("CornerstoneImageRendered",i.onImageRendered),e(n).on("CornerstoneToolsMouseMove",s,a),e(n).on("CornerstoneToolsMouseDown",s,l),e(n).on("CornerstoneToolsMouseDownActivate",s,u),t.updateImage(n)}function d(n,r){var s={mouseButtonMask:r};e(n).off("CornerstoneImageRendered",i.onImageRendered),e(n).off("CornerstoneToolsMouseMove",a),e(n).off("CornerstoneToolsMouseDown",l),e(n).off("CornerstoneToolsMouseDownActivate",u),e(n).on("CornerstoneImageRendered",i.onImageRendered),e(n).on("CornerstoneToolsMouseMove",s,a),e(n).on("CornerstoneToolsMouseDown",s,l),t.updateImage(n)}var v={enable:h,disable:c,activate:p,deactivate:d};return v}return r===undefined&&(r={}),r.mouseButtonRectangleTool=i,r}($,cornerstone,cornerstoneMath,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function r(t){var n={activate:function(n){e(n).off("CornerstoneToolsMouseWheel",t);var r={};e(n).on("CornerstoneToolsMouseWheel",r,t)},disable:function(n){e(n).off("CornerstoneToolsMouseWheel",t)},enable:function(n){e(n).off("CornerstoneToolsMouseWheel",t)},deactivate:function(n){e(n).off("CornerstoneToolsMouseWheel",t)}};return n}return n===undefined&&(n={}),n.mouseWheelTool=r,n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function r(t){var n={activate:function(n,r){e(n).off("CornerstoneToolsTouchDrag",t);var i={};e(n).on("CornerstoneToolsTouchDrag",i,t)},disable:function(n){e(n).off("CornerstoneToolsTouchDrag",t)},enable:function(n){e(n).off("CornerstoneToolsTouchDrag",t)},deactivate:function(n){e(n).off("CornerstoneToolsTouchDrag",t)}};return n}return n===undefined&&(n={}),n.touchDragTool=r,n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function r(t){var n={activate:function(n){e(n).off("CornerstoneToolsTouchPinch",t);var r={};e(n).on("CornerstoneToolsTouchPinch",r,t)},disable:function(n){e(n).off("CornerstoneToolsTouchPinch",t)},enable:function(n){e(n).off("CornerstoneToolsTouchPinch",t)},deactivate:function(n){e(n).off("CornerstoneToolsTouchPinch",t)}};return n}return n===undefined&&(n={}),n.touchPinchTool=r,n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n,r){"use strict";function i(i){function s(t){var n=i.createNewMeasurement(t);r.addToolState(t.element,i.toolType,n),e(t.element).off("CornerstoneToolsTouchDrag",u),r.moveHandle(t,n.handles.end,function(){r.anyHandlesOutsideImage(t,n.handles)&&r.removeToolState(mouseEventData.element,mouseToolInterface.toolType,n),e(t.element).on("CornerstoneToolsTouchDrag",u)})}function o(e,t){return s(t),!1}function u(e,n){r.activeToolcoordinate.setCoords(n);var s=r.getToolState(n.element,i.toolType);if(s===undefined)return;var o=!1;for(var u=0;u<s.data.length;u++){var a=s.data[u];r.handleActivator(a.handles,n.currentPoints.image,n.viewport.scale)===!0&&(o=!0)}o===!0&&t.updateImage(n.element)}function a(e,t){for(var r in e.handles){var i=n.point.distanceSquared(e.handles[r],t);if(i<30)return e.handles[r]}}function f(t,n){function o(){r.anyHandlesOutsideImage(n,s.handles)&&r.removeToolState(n.element,i.toolType,s),e(n.element).on("CornerstoneToolsTouchDrag",u)}var s,f=n.startPoints.image,l=r.getToolState(t.currentTarget,i.toolType),c;if(l!==undefined)for(c=0;c<l.data.length;c++){s=l.data[c];var h=a(s,f);if(h!==undefined)return e(n.element).off("CornerstoneToolsTouchDrag",u),r.touchmoveHandle(n,h,o),t.stopImmediatePropagation(),!1}if(l!==undefined&&i.pointNearTool!==undefined)for(c=0;c<l.data.length;c++){s=l.data[c];if(i.pointNearTool(s,f))return e(n.element).off("CornerstoneToolsTouchDrag",u),r.touchmoveAllHandles(t,s,l,!0),t.stopImmediatePropagation(),!1}}function l(n){e(n).off("CornerstoneImageRendered",i.onImageRendered),e(n).off("CornerstoneToolsTouchDrag",u),e(n).off("CornerstoneToolsDragStart",f),e(n).off("CornerstoneToolsDragStartActive",o),t.updateImage(n)}function c(n){e(n).off("CornerstoneImageRendered",i.onImageRendered),e(n).off("CornerstoneToolsTouchDrag",u),e(n).off("CornerstoneToolsDragStart",f),e(n).off("CornerstoneToolsDragStartActive",o),e(n).on("CornerstoneImageRendered",i.onImageRendered),t.updateImage(n)}function h(n){e(n).off("CornerstoneImageRendered",i.onImageRendered),e(n).off("CornerstoneToolsTouchDrag",u),e(n).off("CornerstoneToolsDragStart",f),e(n).off("CornerstoneToolsDragStartActive",o),e(n).on("CornerstoneImageRendered",i.onImageRendered),e(n).on("CornerstoneToolsTouchDrag",u),e(n).on("CornerstoneToolsDragStart",f),e(n).on("CornerstoneToolsDragStartActive",o),t.updateImage(n)}function p(n){e(n).off("CornerstoneImageRendered",i.onImageRendered),e(n).off("CornerstoneToolsTouchDrag",u),e(n).off("CornerstoneToolsDragStart",f),e(n).off("CornerstoneToolsDragStartActive",o),e(n).on("CornerstoneImageRendered",i.onImageRendered),e(n).on("CornerstoneToolsTouchDrag",u),e(n).on("CornerstoneToolsDragStart",f),t.updateImage(n)}var d={enable:c,disable:l,activate:h,deactivate:p};return d}return r===undefined&&(r={}),r.touchTool=i,r}($,cornerstone,cornerstoneMath,cornerstoneTools),cornerstoneTools=function(e,t,n,r){"use strict";function s(e){var t={visible:!0,handles:{start:{x:e.currentPoints.image.x-20,y:e.currentPoints.image.y+10,highlight:!0,active:!1},end:{x:e.currentPoints.image.x,y:e.currentPoints.image.y,highlight:!0,active:!0},start2:{x:e.currentPoints.image.x-20,y:e.currentPoints.image.y+10,highlight:!0,active:!1},end2:{x:e.currentPoints.image.x,y:e.currentPoints.image.y+20,highlight:!0,active:!1}}};return t}function o(e,t){var r={start:e.handles.start,end:e.handles.end},i=n.lineSegment.distanceToPoint(r,t);return i<5?!0:(r.start=e.handles.start2,r.end=e.handles.end2,i=n.lineSegment.distanceToPoint(r,t),i<5)}function u(e,n){var s=r.getToolState(e.currentTarget,i);if(s===undefined)return;var u=n.canvasContext.canvas.getContext("2d");t.setToPixelCoordinateSystem(n.enabledElement,u);var a=r.activeToolcoordinate.getToolColor();for(var f=0;f<s.data.length;f++){u.save();var l=s.data[f];o(l,r.activeToolcoordinate.getCoords())?a=r.activeToolcoordinate.getActiveColor():a=r.activeToolcoordinate.getToolColor(),u.beginPath(),u.strokeStyle=a,u.lineWidth=1/n.viewport.scale,u.moveTo(l.handles.start.x,l.handles.start.y),u.lineTo(l.handles.end.x,l.handles.end.y),u.moveTo(l.handles.start2.x,l.handles.start2.y),u.lineTo(l.handles.end2.x,l.handles.end2.y),u.stroke(),u.beginPath(),r.drawHandles(u,n,l.handles),u.stroke(),u.fillStyle=a;var c=(Math.ceil(l.handles.start.x)-Math.ceil(l.handles.end.x))*n.image.columnPixelSpacing,h=(Math.ceil(l.handles.start.y)-Math.ceil(l.handles.end.y))*n.image.rowPixelSpacing,p=(Math.ceil(l.handles.start2.x)-Math.ceil(l.handles.end2.x))*n.image.columnPixelSpacing,d=(Math.ceil(l.handles.start2.y)-Math.ceil(l.handles.end2.y))*n.image.rowPixelSpacing,v=Math.acos(Math.abs((c*p+h*d)/(Math.sqrt(c*c+h*h)*Math.sqrt(p*p+d*d))));v*=180/Math.PI;var m=r.roundToDecimal(v,2),g="00B0",y=m.toString()+String.fromCharCode(parseInt(g,16)),b=r.setContextToDisplayFontSize(n.enabledElement,n.canvasContext,15);u.font=""+b.fontSize+"px Arial";var w=(l.handles.start2.x+l.handles.end2.x)/2/b.fontScale,E=(l.handles.start2.y+l.handles.end2.y)/2/b.fontScale;u.fillText(y,w,E),u.restore()}}r===undefined&&(r={});var i="angle";return r.angle=r.mouseButtonTool({createNewMeasurement:s,onImageRendered:u,pointNearTool:o,toolType:i}),r.angleTouch=r.touchTool({createNewMeasurement:s,onImageRendered:u,pointNearTool:o,toolType:i}),r}($,cornerstone,cornerstoneMath,cornerstoneTools),cornerstoneTools=function(e,t,n,r){"use strict";function s(e){var t={visible:!0,handles:{start:{x:e.currentPoints.image.x,y:e.currentPoints.image.y,highlight:!0,active:!1},end:{x:e.currentPoints.image.x,y:e.currentPoints.image.y,highlight:!0,active:!0}}};return t}function o(e,t){var r={left:Math.min(e.handles.start.x,e.handles.end.x),top:Math.min(e.handles.start.y,e.handles.end.y),width:Math.abs(e.handles.start.x-e.handles.end.x),height:Math.abs(e.handles.start.y-e.handles.end.y)},i=n.rect.distanceToPoint(r,t);return i<5}function u(e,t){var n=e.width/2,r=e.height/2;if(n<=0||r<=0)return!1;var i={x:e.left+n,y:e.top+r},s={x:t.x-i.x,y:t.y-i.y},o=s.x*s.y/(n*n)+s.y*s.y/(r*r)<=1;return o}function a(e,t){var n=0,r=0,i=0,s=0;for(var o=t.top;o<t.top+t.height;o++)for(var a=t.left;a<t.left+t.width;a++)u(t,{x:a,y:o})===!0&&(n+=e[s],r+=e[s]*e[s],i++),s++;if(i===0)return{count:i,mean:0,variance:0,stdDev:0};var f=n/i,l=r/i-f*f;return{count:i,mean:f,variance:l,stdDev:Math.sqrt(l)}}function f(e,n){var s=r.getToolState(e.currentTarget,i);if(s===undefined)return;var u=n.canvasContext.canvas.getContext("2d");t.setToPixelCoordinateSystem(n.enabledElement,u);var f=r.activeToolcoordinate.getToolColor();for(var l=0;l<s.data.length;l++){u.save();var c=s.data[l];o(c,r.activeToolcoordinate.getCoords())?f=r.activeToolcoordinate.getActiveColor():f=r.activeToolcoordinate.getToolColor();var h=Math.abs(c.handles.start.x-c.handles.end.x),p=Math.abs(c.handles.start.y-c.handles.end.y),d=Math.min(c.handles.start.x,c.handles.end.x),v=Math.min(c.handles.start.y,c.handles.end.y),m=(c.handles.start.x+c.handles.end.x)/2,g=(c.handles.start.y+c.handles.end.y)/2;u.beginPath(),u.strokeStyle=f,u.lineWidth=1/n.viewport.scale,r.drawEllipse(u,d,v,h,p),u.closePath(),u.beginPath(),r.drawHandles(u,n,c.handles),u.stroke();var y=t.getPixels(n.element,d,v,h,p),b={left:d,top:v,width:h,height:p},w=a(y,b),E=Math.PI*(h*n.image.columnPixelSpacing/2)*(p*n.image.rowPixelSpacing/2),S="Area: "+E.toFixed(2)+" mm^2",x=r.setContextToDisplayFontSize(n.enabledElement,n.canvasContext,15);u.font=""+x.fontSize+"px Arial";var T=u.measureText(E),N=x.lineHeight,C=m<n.image.columns/2?m+h/2:m-h/2-T.width*x.fontScale,k=g<n.image.rows/2?g+p/2:g-p/2;C/=x.fontScale,k/=x.fontScale,u.fillStyle=f,u.fillText("Mean: "+w.mean.toFixed(2),C,k-N),u.fillText("StdDev: "+w.stdDev.toFixed(2),C,k),u.fillText(S,C,k+N),u.restore()}}r===undefined&&(r={});var i="ellipticalRoi";return r.ellipticalRoi=r.mouseButtonTool({createNewMeasurement:s,onImageRendered:f,pointNearTool:o,toolType:i}),r.ellipticalroi_Touch=r.touchTool({createNewMeasurement:s,onImageRendered:f,pointNearTool:o,toolType:i}),r}($,cornerstone,cornerstoneMath,cornerstoneTools),cornerstoneTools=function(e,t,n,r){"use strict";function s(e){var t={visible:!0,handles:{start:{x:e.currentPoints.image.x,y:e.currentPoints.image.y,highlight:!0,active:!1},end:{x:e.currentPoints.image.x,y:e.currentPoints.image.y,highlight:!0,active:!0}}};return t}function o(e,t){var n={left:Math.min(e.handles.start.x,e.handles.end.x),top:Math.min(e.handles.start.y,e.handles.end.y),width:Math.abs(e.handles.start.x-e.handles.end.x),height:Math.abs(e.handles.start.y-e.handles.end.y)},r=!1;return t.x>=n.left&&t.x<=n.left+n.width&&t.y>=n.top&&t.y<=n.top+n.height&&(r=!0),r}function u(e,t){var r={left:Math.min(e.handles.start.x,e.handles.end.x),top:Math.min(e.handles.start.y,e.handles.end.y),width:Math.abs(e.handles.start.x-e.handles.end.x),height:Math.abs(e.handles.start.y-e.handles.end.y)},i=n.rect.distanceToPoint(r,t);return i<5}function a(e,n){var s=r.getToolState(e.currentTarget,i);if(s===undefined)return;var o=n.canvasContext.canvas.getContext("2d");t.setToPixelCoordinateSystem(n.enabledElement,o);var u=r.activeToolcoordinate.getToolColor();o.save();var a=s.data[0],f="white",l="white",c={left:Math.min(a.handles.start.x,a.handles.end.x),top:Math.min(a.handles.start.y,a.handles.end.y),width:Math.abs(a.handles.start.x-a.handles.end.x),height:Math.abs(a.handles.start.y-a.handles.end.y)};o.beginPath(),r.drawHandles(o,n,a.handles,u),o.stroke(),o.beginPath(),o.strokeStyle="transparent",o.rect(0,0,o.canvas.clientWidth,o.canvas.clientHeight),o.rect(c.width+c.left,c.top,-c.width,c.height),o.stroke(),o.fillStyle="rgba(0,0,0,0.7)",o.fill(),o.closePath(),o.beginPath(),o.strokeStyle=u,o.lineWidth=2.5/n.viewport.scale,o.setLineDash([4]),o.strokeRect(c.left,c.top,c.width,c.height),o.restore()}r===undefined&&(r={});var i="highlight",f=!0;return r.highlight=r.mouseButtonRectangleTool({createNewMeasurement:s,onImageRendered:a,pointNearTool:u,pointInsideRect:o,toolType:i},f),r.highlightTouch=r.touchTool({createNewMeasurement:s,onImageRendered:a,pointNearTool:u,pointInsideRect:o,toolType:i},f),r}($,cornerstone,cornerstoneMath,cornerstoneTools),cornerstoneTools=function(e,t,n,r){"use strict";function s(e){var t={visible:!0,handles:{start:{x:e.currentPoints.image.x,y:e.currentPoints.image.y,highlight:!0,active:!1},end:{x:e.currentPoints.image.x,y:e.currentPoints.image.y,highlight:!0,active:!0}}};return t}function o(e,t){var r={start:e.handles.start,end:e.handles.end},i=n.lineSegment.distanceToPoint(r,t);return i<25}function u(e,n){var s=r.getToolState(e.currentTarget,i);if(s===undefined)return;var u=n.canvasContext.canvas.getContext("2d");t.setToPixelCoordinateSystem(n.enabledElement,u);var a=r.activeToolcoordinate.getToolColor();for(var f=0;f<s.data.length;f++){u.save();var l=s.data[f];o(l,r.activeToolcoordinate.getCoords())?a=r.activeToolcoordinate.getActiveColor():a=r.activeToolcoordinate.getToolColor(),u.beginPath(),u.strokeStyle=a,u.lineWidth=1/n.viewport.scale,u.moveTo(l.handles.start.x,l.handles.start.y),u.lineTo(l.handles.end.x,l.handles.end.y),u.stroke(),u.beginPath(),r.drawHandles(u,n,l.handles,a),u.stroke(),u.fillStyle=a;var c=(l.handles.start.x-l.handles.end.x)*n.image.columnPixelSpacing,h=(l.handles.start.y-l.handles.end.y)*n.image.rowPixelSpacing,p=Math.sqrt(c*c+h*h),d=""+p.toFixed(2)+" mm",v=r.setContextToDisplayFontSize(n.enabledElement,n.canvasContext,15);u.font=""+v.fontSize+"px Arial";var m=(l.handles.start.x+l.handles.end.x)/2/v.fontScale,g=(l.handles.start.y+l.handles.end.y)/2/v.fontScale;u.fillText(d,m,g),u.restore()}}r===undefined&&(r={});var i="length";return r.length=r.mouseButtonTool({createNewMeasurement:s,onImageRendered:u,pointNearTool:o,toolType:i}),r.lengthTouch=r.touchTool({createNewMeasurement:s,onImageRendered:u,pointNearTool:o,toolType:i}),r}($,cornerstone,cornerstoneMath,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function r(t,n){e(n.element).off("CornerstoneToolsMouseDrag",s),e(n.element).off("CornerstoneToolsMouseUp",r)}function i(t,i){if(n.isMouseButtonEnabled(i.which,t.data.mouseButtonMask))return e(i.element).on("CornerstoneToolsMouseDrag",s),e(i.element).on("CornerstoneToolsMouseUp",r),!1}function s(e,n){return n.viewport.translation.x+=n.deltaPoints.page.x/n.viewport.scale,n.viewport.translation.y+=n.deltaPoints.page.y/n.viewport.scale,t.setViewport(n.element,n.viewport),!1}function o(e,n){var r=n;return r.viewport.translation.x+=r.deltaPoints.page.x/r.viewport.scale,r.viewport.translation.y+=r.deltaPoints.page.y/r.viewport.scale,t.setViewport(r.element,r.viewport),!1}return n===undefined&&(n={}),n.pan=n.simpleMouseButtonTool(i),n.panTouchDrag=n.touchDragTool(o),n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function i(e){var t={visible:!0,handles:{end:{x:e.currentPoints.image.x,y:e.currentPoints.image.y,highlight:!0,active:!0}}};return t}function s(e,t){if(e.data===undefined)return undefined;if(e.data.string("x00080060")!=="PT")return undefined;var n=t*e.slope+e.intercept,r=e.data.floatString("x00101030");if(r===undefined)return undefined;var i=e.data.elements.x00540016;if(i===undefined)return undefined;i=i.items[0].dataSet;var s=i.time("x00181072"),o=i.floatString("x00181074"),u=i.floatString("x00181075"),a=e.data.time("x00080032");if(s===undefined||o===undefined||u===undefined||a===undefined)return undefined;var f=a.fractionalSeconds+a.seconds+a.minutes*60+a.hours*60*60,l=s.fractionalSeconds+s.seconds+s.minutes*60+s.hours*60*60,c=f-l,h=o*Math.exp(-c*Math.log(2)/u),p=n*r/h*1e3;return p}function o(e,i){var o=n.getToolState(e.currentTarget,r);if(o===undefined)return;var u=i.canvasContext.canvas.getContext("2d");t.setToPixelCoordinateSystem(i.enabledElement,u);var a="white";for(var f=0;f<o.data.length;f++){u.save();var l=o.data[f];u.beginPath(),n.drawHandles(u,i,l.handles,a),u.stroke();var c=n.setContextToDisplayFontSize(i.enabledElement,i.canvasContext,15);u.font=""+c.fontSize+"px Arial";var h=Math.round(l.handles.end.x),p=Math.round(l.handles.end.y);d=l.handles.end.x+3,v=l.handles.end.y-3;var d=d/c.fontScale,v=v/c.fontScale;u.fillStyle="white";var m=t.getStoredPixels(i.element,h,p,1,1),g=m[0],y=g*i.image.slope+i.image.intercept,b=s(i.image,g);u.fillText(""+h+","+p,d,v);var w="SP: "+g+" MO: "+y.toFixed(3);b!==undefined&&(w+=" SUV: "+b.toFixed(3)),u.fillText(w,d,v+c.lineHeight),u.restore()}}n===undefined&&(n={});var r="probe";return n.probe=n.mouseButtonTool({createNewMeasurement:i,onImageRendered:o,toolType:r}),n.probeTouch=n.touchTool({createNewMeasurement:i,onImageRendered:o,toolType:r}),n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n,r){"use strict";function s(e){var t={visible:!0,handles:{start:{x:e.currentPoints.image.x,y:e.currentPoints.image.y,highlight:!0,active:!1},end:{x:e.currentPoints.image.x,y:e.currentPoints.image.y,highlight:!0,active:!0}}};return t}function o(e,t){var r={left:Math.min(e.handles.start.x,e.handles.end.x),top:Math.min(e.handles.start.y,e.handles.end.y),width:Math.abs(e.handles.start.x-e.handles.end.x),height:Math.abs(e.handles.start.y-e.handles.end.y)},i=n.rect.distanceToPoint(r,t);return i<5}function u(e,t){var n=0,r=0,i=0,s=0;for(var o=t.top;o<t.top+t.height;o++)for(var u=t.left;u<t.left+t.width;u++)n+=e[s],r+=e[s]*e[s],i++,s++;if(i===0)return{count:i,mean:0,variance:0,stdDev:0};var a=n/i,f=r/i-a*a;return{count:i,mean:a,variance:f,stdDev:Math.sqrt(f)}}function a(e,n){var s=r.getToolState(e.currentTarget,i);if(s===undefined)return;var a=n.canvasContext.canvas.getContext("2d");t.setToPixelCoordinateSystem(n.enabledElement,a);var f=r.activeToolcoordinate.getToolColor();for(var l=0;l<s.data.length;l++){a.save();var c=s.data[l];o(c,r.activeToolcoordinate.getCoords())?f=r.activeToolcoordinate.getActiveColor():f=r.activeToolcoordinate.getToolColor();var h=Math.abs(c.handles.start.x-c.handles.end.x),p=Math.abs(c.handles.start.y-c.handles.end.y),d=Math.min(c.handles.start.x,c.handles.end.x),v=Math.min(c.handles.start.y,c.handles.end.y),m=(c.handles.start.x+c.handles.end.x)/2,g=(c.handles.start.y+c.handles.end.y)/2;a.beginPath(),a.strokeStyle=f,a.lineWidth=1/n.viewport.scale,a.rect(d,v,h,p),a.stroke(),a.beginPath(),r.drawHandles(a,n,c.handles,f),a.stroke();var y=t.getPixels(n.element,d,v,h,p),b={left:d,top:v,width:h,height:p},w=u(y,b),E=h*n.image.columnPixelSpacing*p*n.image.rowPixelSpacing,S="Area: "+E.toFixed(2)+" mm^2",x=r.setContextToDisplayFontSize(n.enabledElement,n.canvasContext,15);a.font=""+x.fontSize+"px Arial";var T=a.measureText(E),N=x.lineHeight,C=m<n.image.columns/2?m+h/2:m-h/2-T.width*x.fontScale,k=g<n.image.rows/2?g+p/2:g-p/2;C/=x.fontScale,k/=x.fontScale,a.fillStyle=f,a.fillText("Mean: "+w.mean.toFixed(2),C,k-N),a.fillText("StdDev: "+w.stdDev.toFixed(2),C,k),a.fillText(S,C,k+N),a.restore()}}r===undefined&&(r={});var i="rectangleRoi";return r.rectangleRoi=r.mouseButtonTool({createNewMeasurement:s,onImageRendered:a,pointNearTool:o,toolType:i}),r.rectangleRoiTouch=r.touchTool({createNewMeasurement:s,onImageRendered:a,pointNearTool:o,toolType:i}),r}($,cornerstone,cornerstoneMath,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function r(t,n){e(n.element).off("CornerstoneToolsMouseDrag",s),e(n.element).off("CornerstoneToolsMouseUp",r)}function i(t,i){if(n.isMouseButtonEnabled(i.which,t.data.mouseButtonMask))return e(i.element).on("CornerstoneToolsMouseDrag",s),e(i.element).on("CornerstoneToolsMouseUp",r),!1}function s(e,n){var r=n.image.maxPixelValue-n.image.minPixelValue,i=r/1024;return n.viewport.voi.windowWidth+=n.deltaPoints.page.x*i,n.viewport.voi.windowCenter+=n.deltaPoints.page.y*i,t.setViewport(n.element,n.viewport),!1}function o(e,n){var r=n,i=r.image.maxPixelValue-r.image.minPixelValue,s=i/1024;r.viewport.voi.windowWidth+=r.deltaPoints.page.x*s,r.viewport.voi.windowCenter+=r.deltaPoints.page.y*s,t.setViewport(r.element,r.viewport)}return n===undefined&&(n={}),n.wwwc=n.simpleMouseButtonTool(i),n.wwwcTouchDrag=n.touchDragTool(o),n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function r(e,n,r){var i=1.7,s=Math.log(n.scale)/Math.log(i),o=s+r,u=Math.pow(i,o);n.scale=u,t.setViewport(e,n)}function i(t,n){e(n.element).off("CornerstoneToolsMouseDrag",o),e(n.element).off("CornerstoneToolsMouseUp",i)}function s(t,r){if(n.isMouseButtonEnabled(r.which,t.data.mouseButtonMask))return e(r.element).on("CornerstoneToolsMouseDrag",o),e(r.element).on("CornerstoneToolsMouseUp",i),!1}function o(e,n){var i=n.deltaPoints.page.y/100;r(n.element,n.viewport,i);var s=t.pageToPixel(n.element,n.startPoints.page.x,n.startPoints.page.y);return n.viewport.translation.x-=n.startPoints.image.x-s.x,n.viewport.translation.y-=n.startPoints.image.y-s.y,t.setViewport(n.element,n.viewport),!1}function u(e,t){var n=-t.direction/4;r(t.element,t.viewport,n)}function a(e,t){var n=t;r(n.element,n.viewport,n.direction/4)}function f(e,n){var i=n,s=i.deltaPoints.page.y/100;r(i.element,i.viewport,s);var o=t.pageToPixel(i.element,i.startPoints.page.x,i.startPoints.page.y);return i.viewport.translation.x-=i.startPoints.image.x-o.x,i.viewport.translation.y-=i.startPoints.image.y-o.y,t.setViewport(i.element,i.viewport),!1}return n===undefined&&(n={}),n.zoom=n.simpleMouseButtonTool(s),n.zoomWheel=n.mouseWheelTool(u),n.zoomTouchPinch=n.touchPinchTool(a),n.zoomTouchDrag=n.touchDragTool(f),n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n,r){"use strict";function l(t){e(t.element).trigger("CornerstoneToolsDragStartActive",t)}function c(c){c.gesture.preventDefault(),c.gesture.stopPropagation();if(s===!0)return;var h=c.currentTarget,p;if(c.type==="transform"){var d=i-c.gesture.scale;i=c.gesture.scale;var v={event:c,viewport:t.getViewport(h),mage:t.getEnabledElement(h).image,element:h,direction:d<0?1:-1};p=jQuery.Event("CornerstoneToolsTouchPinch",v),e(v.element).trigger(p,v)}else if(c.type==="touch"){o={page:n.point.pageToPoint(c.gesture.touches[0]),image:t.pageToPixel(h,c.gesture.touches[0].pageX,c.gesture.touches[0].pageY)},a={event:c,viewport:t.getViewport(h),image:t.getEnabledElement(h).image,element:h,startPoints:o,lastPoints:u,currentPoints:o,deltaPoints:{x:0,y:0}},p=jQuery.Event("CornerstoneToolsDragStart",a),e(a.element).trigger(p,a),u=r.copyPoints(o);if(p.isImmediatePropagationStopped()===!1&&l(a)===!0)return r.pauseEvent(c)}else{if(c.type!=="drag"){if(c.type==="dragend"){var m={page:n.point.pageToPoint(c.gesture.touches[0]),image:t.pageToPixel(h,c.gesture.touches[0].pageX,c.gesture.touches[0].pageY)},g={page:n.point.subtract(m.page,u.page),image:n.point.subtract(m.image,u.image)};return f={event:c,viewport:t.getViewport(h),image:t.getEnabledElement(h).image,element:h,startPoints:o,lastPoints:u,currentPoints:m,deltaPoints:g},p=jQuery.Event("CornerstoneToolsDragEnd",f),e(a.element).trigger(p,f),r.pauseEvent(c)}return}m={page:n.point.pageToPoint(c.gesture.touches[0]),image:t.pageToPixel(h,c.gesture.touches[0].pageX,c.gesture.touches[0].pageY)},g={page:n.point.subtract(m.page,u.page),image:n.point.subtract(m.image,u.image)},f={viewport:t.getViewport(h),image:t.getEnabledElement(h).image,element:h,startPoints:o,lastPoints:u,currentPoints:m,deltaPoints:g},e(a.element).trigger("CornerstoneToolsTouchDrag",f),u=r.copyPoints(m)}s=!1}function h(t){var n={transform_always_block:!0,transform_min_scale:.01,drag_block_horizontal:!0,drag_block_vertical:!0,drag_min_distance:0};e(t).hammer(n).on("touch drag transform dragstart dragend",c)}function p(t){e(t).hammer().off("touch drag transform dragstart dragend",c)}r===undefined&&(r={});var i=1,s=!1,o,u,a,f;return r.touchInput={enable:h,disable:p},r}($,cornerstone,cornerstoneMath,cornerstoneTools),cornerstoneTools=function(e,t,n,r){"use strict";function i(e,t){var r=e.image,i={left:0,top:0,width:r.width,height:r.height},s=!1;for(var o in t){var u=t[o];n.point.insideRect(u,i)===!1&&(s=!0)}return s}return r===undefined&&(r={}),r.anyHandlesOutsideImage=i,r}($,cornerstone,cornerstoneMath,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function i(e,t,n,i){e.strokeStyle=i;var s=r/t.viewport.scale;for(var o in n){var u=n[o];if(u.active||u.highlight)e.beginPath(),u.active?e.lineWidth=2/t.viewport.scale:e.lineWidth=.5/t.viewport.scale,e.arc(u.x,u.y,s,0,2*Math.PI),e.stroke()}}n===undefined&&(n={});var r=6;return n.drawHandles=i,n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n,r){"use strict";function s(e,t,r){var s=i/r;for(var o in e){var u=e[o],a=n.point.distance(t,u);if(a<=s)return u}return undefined}function o(e){for(var t in e){var n=e[t];if(n.active===!0)return n}return undefined}function u(e,t,n){var r=o(e),i=s(e,t,n);return r!==i?(i!==undefined&&(i.active=!0),r!==undefined&&(r.active=!1),!0):!1}r===undefined&&(r={});var i=6;return r.handleActivator=u,r}($,cornerstone,cornerstoneMath,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function r(n,r,i,s){function u(e,n){r.x=n.currentPoints.image.x,r.y=n.currentPoints.image.y,s&&(r.x<0&&(r.x=0),r.x>n.image.width&&(r.x=n.image.width),r.y<0&&(r.y=0),r.y>n.image.height&&(r.y=n.image.height)),t.updateImage(o)}function a(n,s){r.eactive=!1,e(o).off("CornerstoneToolsMouseDrag",u),e(o).off("CornerstoneToolsMouseUp",a),t.updateImage(o),i()}var o=n.element;e(o).on("CornerstoneToolsMouseDrag",u),e(o).on("CornerstoneToolsMouseUp",a)}return n===undefined&&(n={}),n.moveHandle=r,n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function r(n,r,i){function o(e,n){var i=n;r.x=i.currentPoints.image.x,r.y=i.currentPoints.image.y,t.updateImage(s)}function u(n){r.eactive=!1,e(s).off("CornerstoneToolsTouchDrag",o),e(s).off("CornerstoneToolsDragEnd",u),t.updateImage(s),i()}var s=n.element;e(s).on("CornerstoneToolsTouchDrag",o),e(s).on("CornerstoneToolsDragEnd",u)}return n===undefined&&(n={}),n.touchmoveHandle=r,n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n,r){"use strict";function i(r,i,s,o,u){function l(e,n){for(var r in i.handles){var s=i.handles[r];s.x+=n.deltaPoints.image.x,s.y+=n.deltaPoints.image.y,u&&(s.x<0&&(s.x=0),s.x>n.image.width&&(s.x=n.image.width),s.y<0&&(s.y=0),s.y>n.image.height&&(s.y=n.image.height))}return t.updateImage(f),!1}function c(r,u){i.moving=!1,e(f).off("CornerstoneToolsMouseDrag",l),e(f).off("CornerstoneToolsMouseUp",c);if(o===!0){var a=u.image,h=!1,p={top:0,left:0,width:a.width,height:a.height};for(var d in i.handles){var v=i.handles[d];n.point.insideRect(v,p)===!1&&(h=!0)}if(h){var m=-1;for(var g=0;g<s.data.length;g++)s.data[g]===i&&(m=g);m!==-1&&s.data.splice(m,1)}}t.updateImage(f)}var a=r,f=a.element;return e(f).on("CornerstoneToolsMouseDrag",l),e(f).on("CornerstoneToolsMouseUp",c),!0}return r===undefined&&(r={}),r.moveAllHandles=i,r}($,cornerstone,cornerstoneMath,cornerstoneTools),cornerstoneTools=function(e,t,n,r){"use strict";function i(r,i,s,o){function f(e,n){var r=n;for(var s in i.handles){var o=i.handles[s];o.x+=r.deltaPoints.image.x,o.y+=r.deltaPoints.image.y}return t.updateImage(a),!1}function l(r,u){i.moving=!1;var c=u;e(a).off("CornerstoneToolsTouchDrag",f),e(a).off("CornerstoneToolsDragEnd",l);if(o===!0){var h=c.image,p=!1,d={top:0,left:0,width:h.width,height:h.height};for(var v in i.handles){var m=i.handles[v];n.point.insideRect(m,d)===!1&&(p=!0)}if(p){var g=-1;for(var y=0;y<s.data.length;y++)s.data[y]===i&&(g=y);g!==-1&&s.data.splice(g,1)}}t.updateImage(a)}var u=r,a=u.element;return e(a).on("CornerstoneToolsTouchDrag",f),e(a).on("CornerstoneToolsDragEnd",l),!0}return r===undefined&&(r={}),r.touchmoveAllHandles=i,r}($,cornerstone,cornerstoneMath,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function r(){var t=this;t.samples=[],this.set=function(n){t.samples=n,e(t).trigger("CornerstoneLineSampleUpdated")}}return n===undefined&&(n={}),n.LineSampleMeasurement=r,n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function r(){var t=this;t.measurements=[],this.add=function(n){var r=t.measurements.push(n),i={index:r,measurement:n};e(t).trigger("CornerstoneMeasurementAdded",i)},this.remove=function(n){var r=t.measurements[n];t.measurements.splice(n,1);var i={index:n,measurement:r};e(t).trigger("CornerstoneMeasurementRemoved",i)}}return n===undefined&&(n={}),n.MeasurementManager=new r,n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function i(e){r.push(e)}function s(e){var t=r.indexOf(e);if(t===-1)return;r.splice(t,1)}function o(t,n){var i;return e.each(r,function(e,r){i=r(t,n);if(i!==undefined)return!0}),i}n===undefined&&(n={});var r=[];return n.metaData={addProvider:i,removeProvider:s,get:o},n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function r(e,t){var r=t.imagePositionPatient,i=n.projectPatientPointToImagePlane(r,e),s=n.imagePointToPatientPoint({x:t.columns,y:t.rows},t),o=n.projectPatientPointToImagePlane(s,e),u={start:{x:i.x,y:i.y},end:{x:o.x,y:o.y}};return u}return n===undefined&&(n={}),n.referenceLines===undefined&&(n.referenceLines={}),n.referenceLines.calculateReferenceLine=r,n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function i(i,s){var o=n.getToolState(i.currentTarget,r);if(o===undefined)return;var u=o.data[0].synchronizationContext,a=u.getSourceElements(),f=o.data[0].renderer,l=s.canvasContext.canvas.getContext("2d");t.setToPixelCoordinateSystem(s.enabledElement,l),e.each(a,function(e,t){if(t===i.currentTarget)return;f(l,s,i.currentTarget,t)})}function s(s,o,u){u=u||n.referenceLines.renderActiveReferenceLine,n.addToolState(s,r,{synchronizationContext:o,renderer:u}),e(s).on("CornerstoneImageRendered",i),t.updateImage(s)}function o(n,r){e(n).off("CornerstoneImageRendered",i),t.updateImage(n)}n===undefined&&(n={}),n.referenceLines===undefined&&(n.referenceLines={});var r="referenceLines";return n.referenceLines.tool={enable:s,disable:o},n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function r(e,r,i,s){var o=t.getEnabledElement(i).image,u=t.getEnabledElement(s).image;if(o===undefined||u===undefined)return;var a=n.metaData.get("imagePlane",o.imageId),f=n.metaData.get("imagePlane",u.imageId);if(a.frameOfReferenceUID!=f.frameOfReferenceUID)return;var l=a.rowCosines.clone().cross(a.columnCosines),c=f.rowCosines.clone().cross(f.columnCosines),h=l.angleTo(c);h=Math.abs(h);if(h<.5)return;var p=n.referenceLines.calculateReferenceLine(a,f),d=n.activeToolcoordinate.getActiveColor();e.beginPath(),e.strokeStyle=d,e.lineWidth=1/r.viewport.scale,e.moveTo(p.start.x,p.start.y),e.lineTo(p.end.x,p.end.y),e.stroke()}return n===undefined&&(n={}),n.referenceLines===undefined&&(n.referenceLines={}),n.referenceLines.renderActiveReferenceLine=r,n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function i(e,i){if(e===undefined)throw"playClip: element must not be undefined";i===undefined&&(i=30);var s=n.getToolState(e,"stack");if(s===undefined||s.data===undefined||s.data.length===0)return;var o=s.data[0],u=n.getToolState(e,r),a;u===undefined||u.data.length===0?(a={intervalId:undefined,framesPerSecond:i,lastFrameTimeStamp:undefined,frameRate:0},n.addToolState(e,r,a)):(a=u.data[0],a.framesPerSecond=i);if(a.intervalId!==undefined)return;a.intervalId=setInterval(function(){var n=o.currentImageIdIndex;a.framesPerSecond>0?n++:n--,n>=o.imageIds.length&&(n=0),n<0&&(n=o.imageIds.length-1);if(n!==o.currentImageIdIndex){var r=t.getViewport(e);t.loadAndCacheImage(o.imageIds[n]).then(function(i){o.currentImageIdIndex=n,t.displayImage(e,i,r)})}},1e3/Math.abs(a.framesPerSecond))}function s(e){var t=n.getToolState(e,r),i;if(t===undefined||t.data.length===0)return;i=t.data[0],clearInterval(i.intervalId),i.intervalId=undefined}n===undefined&&(n={});var r="playClip";return n.playClip=i,n.stopClip=s,n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function i(e){var s=n.getToolState(e,"stack");if(s===undefined||s.data===undefined||s.data.length===0)return;var o=n.getToolState(e,r);if(o===undefined)return;var u=o.data[0],a=s.data[0];if(a.enabled===!1)return;var f=u.prefetchImageIdIndex+1;f=Math.min(a.imageIds.length-1,f),f=Math.max(0,f);if(f===u.prefetchImageIdIndex){u.enabled=!1;return}u.prefetchImageIdIndex=f;var l=a.imageIds[f],c=t.loadAndCacheImage(l);c.done(function(t){if(a.enabled===!1)return;setTimeout(function(){i(e)},1)})}function s(e){var t=n.getToolState(e,r);t===undefined&&(t={prefetchImageIdIndex:0,enabled:!0},n.addToolState(e,r,t)),i(e)}function o(e){var t=n.getToolState(e,r);t===undefined?(t={prefetchImageIdIndex:0,enabled:!1},n.removeToolState(e,r,t)):t.enabled=!1}n===undefined&&(n={});var r="stackPrefetch";return n.stackPrefetch={enable:s,disable:o},n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function i(e,r){var i=n.getToolState(e,"stack");if(i===undefined||i.data===undefined||i.data.length===0)return;var s=i.data[0],o=s.currentImageIdIndex+r;o=Math.min(s.imageIds.length-1,o),o=Math.max(0,o);if(o!==s.currentImageIdIndex){var u=t.getViewport(e);t.loadAndCacheImage(s.imageIds[o]).then(function(n){s=i.data[0],s.newImageIdIndex!==o&&(s.currentImageIdIndex=o,t.displayImage(e,n,u))})}}function s(t,n){e(n.element).off("CornerstoneToolsMouseDrag",u),e(n.element).off("CornerstoneToolsMouseUp",s)}function o(t,r){if(n.isMouseButtonEnabled(r.which,t.data.mouseButtonMask)){var i={deltaY:0,options:t.data.options};return e(r.element).on("CornerstoneToolsMouseDrag",i,u),e(r.element).on("CornerstoneToolsMouseUp",s),t.stopImmediatePropagation(),!1}}function u(r,i){r.data.deltaY+=i.deltaPoints.page.y;var s=n.getToolState(i.element,"stack");if(s===undefined||s.data===undefined||s.data.length===0)return;var o=s.data[0],u=e(i.element).height()/o.imageIds.length;r.data.options!==undefined&&r.data.options.stackScrollSpeed!==undefined&&(u=r.data.options.stackScrollSpeed);if(r.data.deltaY>=u||r.data.deltaY<=-u){var a=r.data.deltaY/u,f=r.data.deltaY%u,l=Math.round(a);r.data.deltaY=f;var c=o.currentImageIdIndex+l;c=Math.min(o.imageIds.length-1,c),c=Math.max(0,c);if(c!==o.currentImageIdIndex){o.currentImageIdIndex=c;var h=t.getViewport(i.element);t.loadAndCacheImage(o.imageIds[c]).then(function(e){var n=s.data[0];n.currentImageIdIndex===c&&t.displayImage(i.element,e,h)})}}return!1}function a(e,t){var n=-t.direction;i(t.element,n)}function f(e){var r=e.originalEvent.detail,i={deltaY:0};i.deltaY+=r.deltaPoints.page.y;var s=n.getToolState(r.element,"stack");if(s===undefined||s.data===undefined||s.data.length===0)return;var o=s.data[0];if(i.deltaY>=3||i.deltaY<=-3){var u=i.deltaY/3,a=i.deltaY%3,f=Math.round(u);i.deltaY=a;var l=o.currentImageIdIndex+f;l=Math.min(o.imageIds.length-1,l),l=Math.max(0,l);if(l!==o.currentImageIdIndex){o.currentImageIdIndex=l;var c=t.getViewport(r.element);t.loadAndCacheImage(o.imageIds[l]).then(function(e){t.displayImage(r.element,e,c)})}}return!1}n===undefined&&(n={});var r="stackScroll";return n.stackScroll=n.simpleMouseButtonTool(o),n.stackScrollWheel=n.mouseWheelTool(a),n.stackScrollTouchDrag=n.touchDragTool(f),n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function r(){function r(t){e=t.currentPoints.image}function i(){return e}function s(e){t=e}function o(){return t}function u(e){n=e}function a(){return n}var e="",t="greenyellow",n="white",f={setToolColor:u,setActiveColor:s,getToolColor:a,getActiveColor:o,setCoords:r,getCoords:i};return f}function i(){function n(n,r,i){var s=t.getEnabledElement(n);e.hasOwnProperty(s.image.imageId)===!1&&(e[s.image.imageId]={});var o=e[s.image.imageId];o.hasOwnProperty(r)===!1&&(o[r]={data:[]});var u=o[r];u.data.push(i)}function r(n,r){var i=t.getEnabledElement(n);if(e.hasOwnProperty(i.image.imageId)===!1)return undefined;var s=e[i.image.imageId];if(s.hasOwnProperty(r)===!1)return undefined;var o=s[r];return o}var e={},i={get:r,add:n};return i}n===undefined&&(n={});var s=i(),o=r();return n.newImageIdSpecificToolStateManager=i,n.globalImageIdSpecificToolStateManager=s,n.activeToolcoordinate=o,n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function r(e,n){function i(i,s,o){if(!(e.indexOf(s)>=0))return n.add(i,s,o);var u=t.getEnabledElement(i);r.hasOwnProperty(s)===!1&&(r[s]={data:[]});var a=r[s];a.data.push(o)}function s(t,i){if(e.indexOf(i)>=0){r.hasOwnProperty(i)===!1&&(r[i]={data:[]});var s=r[i];return s}return n.get(t,i)}var r={},o={get:s,add:i};return o}function s(e){var t=n.getElementToolStateManager(e);t===undefined&&(t=n.globalImageIdSpecificToolStateManager);var r=["stack","stackScroll","playClip","volume","slab","referenceLines"],s=n.newStackSpecificToolStateManager(r,t);i.push(s),n.setElementToolStateManager(e,s)}n===undefined&&(n={});var i=[];return n.newStackSpecificToolStateManager=r,n.addStackStateManager=s,n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function r(e,n){function i(i,s,o){if(!(e.indexOf(s)>=0))return n.add(i,s,o);var u=t.getEnabledElement(i);r.hasOwnProperty(s)===!1&&(r[s]={data:[]});var a=r[s];a.data.push(o)}function s(t,i){if(e.indexOf(i)>=0){r.hasOwnProperty(i)===!1&&(r[i]={data:[]});var s=r[i];return s}return n.get(t,i)}var r={},o={get:s,add:i};return o}function s(e,t){t=t||["timeSeries"];var r=n.getElementToolStateManager(e);r===undefined&&(r=n.globalImageIdSpecificToolStateManager);var s=n.newTimeSeriesSpecificToolStateManager(t,r);i.push(s),n.setElementToolStateManager(e,s)}n===undefined&&(n={});var i=[];return n.newTimeSeriesSpecificToolStateManager=r,n.addTimeSeriesStateManager=s,n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function r(e){var r=t.getEnabledElement(e);return r.toolStateManager===undefined&&(r.toolStateManager=n.globalImageIdSpecificToolStateManager),r.toolStateManager}function i(e,t,n){var i=r(e);i.add(e,t,n)}function s(e,t){var n=r(e);return n.get(e,t)}function o(e,t,n){var i=r(e),s=i.get(e,t),o=-1;for(var u=0;u<s.data.length;u++)s.data[u]===n&&(o=u);o!==-1&&s.data.splice(o,1)}function u(e,n){var r=t.getEnabledElement(e);r.toolStateManager=n}return n===undefined&&(n={}),n.addToolState=i,n.getToolState=s,n.removeToolState=o,n.setElementToolStateManager=u,n.getElementToolStateManager=r,n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function r(e,n,r){if(r===n)return;var i=t.getViewport(n),s=t.getViewport(r);if(s.scale===i.scale&&s.translation.x===i.translation.x&&s.translation.y===i.translation.y)return;s.scale=i.scale,s.translation.x=i.translation.x,s.translation.y=i.translation.y,e.setViewport(r,s)}return n===undefined&&(n={}),n.panZoomSynchronizer=r,n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function r(e,r,i){if(i===r)return;var s=n.getToolState(r,"stack"),o=s.data[0],u=n.getToolState(i,"stack"),a=u.data[0],f=o.currentImageIdIndex;f=Math.min(Math.max(f,0),a.imageIds.length-1);if(f===a.currentImageIdIndex)return;t.loadAndCacheImage(a.imageIds[f]).then(function(n){var r=t.getViewport(i);a.currentImageIdIndex=f,e.displayImage(i,n,r)})}return n===undefined&&(n={}),n.stackImageIndexSynchronizer=r,n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function r(r,i,s){if(s===i)return;var o=t.getEnabledElement(i).image,u=n.metaData.get("imagePlane",o.imageId),a=u.imagePositionPatient,f=n.getToolState(s,"stack"),l=f.data[0],c=Number.MAX_VALUE,h=-1;e.each(l.imageIds,function(e,t){var r=n.metaData.get("imagePlane",t),i=r.imagePositionPatient,s=i.distanceToSquared(a);s<c&&(c=s,h=e)});if(h===l.currentImageIdIndex)return;h!==-1&&t.loadAndCacheImage(l.imageIds[h]).then(function(e){var n=t.getViewport(s);l.currentImageIdIndex=h,r.displayImage(s,e,n)})}return n===undefined&&(n={}),n.stackImagePositionSynchronizer=r,n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function r(n,r){function a(t){u=!0,e.each(o,function(e,n){r(i,t,n)}),u=!1}function f(e){if(u===!0)return;a(e.currentTarget)}var i=this,s=[],o=[],u=!1;this.addSource=function(t){var r=s.indexOf(t);if(r!==-1)return;s.push(t),e(t).on(n,f),a(t)},this.addTarget=function(e){var t=o.indexOf(e);if(t!==-1)return;o.push(e),r(i,e,e)},this.add=function(e){i.addSource(e),i.addTarget(e)},this.removeSource=function(t){var r=s.indexOf(t);if(r===-1)return;s.splice(r,1),e(t).off(n,f),a(t)},this.removeTarget=function(e){var t=o.indexOf(e);if(t===-1)return;o.splice(t,1),r(i,e,e)},this.remove=function(e){i.removeTarget(e),i.removeSource(e)},this.getSourceElements=function(){return s},this.displayImage=function(e,n,r){u=!0,t.displayImage(e,n,r),u=!1},this.setViewport=function(e,n){u=!0,t.setViewport(e,n),u=!1}}return n===undefined&&(n={}),n.Synchronizer=r,n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function r(e,n,r){if(r===n)return;t.updateImage(r)}return n===undefined&&(n={}),n.updateImageSynchronizer=r,n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function r(e,n,r){if(r===n)return;var i=t.getViewport(n),s=t.getViewport(r);if(s.voi.windowWidth===i.voi.windowWidth&&s.voi.windowCenter===i.voi.windowCenter&&s.invert===i.invert)return;s.voi.windowWidth=i.voi.windowWidth,s.voi.windowCenter=i.voi.windowCenter,s.invert=i.invert,e.setViewport(r,s)}return n===undefined&&(n={}),n.wwwcSynchronizer=r,n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function i(e){var n=[];e.timeSeries.stacks.forEach(function(r){t.loadAndCacheImage(r.imageIds[e.imageIdIndex]).then(function(t){var r=Math.round(e.handles.end.x)+Math.round(e.handles.end.y)*t.width,i=t.getPixelData()[r];n.push(i)})}),e.lineSample.set(n)}function s(e){var t=n.getToolState(e.element,"timeSeries");if(t===undefined||t.data===undefined||t.data.length===0)return;var r=t.data[0],s={timeSeries:r,lineSample:new n.LineSampleMeasurement,imageIdIndex:r.stacks[r.currentStackIndex].currentImageIdIndex,visible:!0,handles:{end:{x:e.currentPoints.image.x,y:e.currentPoints.image.y,highlight:!0,active:!0}}};return i(s),n.MeasurementManager.add(s),s}function o(e,i){var s=n.getToolState(e.currentTarget,r);if(s===undefined)return;var o=i.canvasContext.canvas.getContext("2d");t.setToPixelCoordinateSystem(i.enabledElement,o);var u="white";for(var a=0;a<s.data.length;a++){o.save();var f=s.data[a];o.beginPath(),n.drawHandles(o,i,f.handles,u),o.stroke();var l=n.setContextToDisplayFontSize(i.enabledElement,i.canvasContext,15);o.font=""+l.fontSize+"px Arial";var c=Math.round(f.handles.end.x),h=Math.round(f.handles.end.y);p=f.handles.end.x+3,d=f.handles.end.y-3;var p=p/l.fontScale,d=d/l.fontScale;o.fillStyle="white",o.fillText(""+c+","+h,p,d),o.restore()}}n===undefined&&(n={});var r="probe4D";return n.probeTool4D=n.mouseButtonTool({createNewMeasurement:s,onImageRendered:o,toolType:r}),n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function i(e,r,i){var s=n.getToolState(e,"timeSeries");if(s===undefined||s.data===undefined||s.data.length===0)return;var o=s.data[0],u=o.stacks[o.currentStackIndex],a=u.currentImageIdIndex,f=o.currentStackIndex+r;i?(f>=o.stacks.length&&(f=0),f<0&&(f=o.stacks.length-1)):(f=Math.min(o.stacks.length-1,f),f=Math.max(0,f));if(f!==o.currentStackIndex){var l=t.getViewport(e),c=o.stacks[f];t.loadAndCacheImage(c.imageIds[a]).then(function(n){o.currentImageIdIndex!==a&&(c.currentImageIdIndex=a,o.currentStackIndex=f,t.displayImage(e,n,l))})}}n===undefined&&(n={});var r="timeSeriesScroll";return n.incrementTimePoint=i,n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function i(e,t){if(e===undefined)throw"playClip: element must not be undefined";t===undefined&&(t=30);var i=n.getToolState(e,"timeSeries");if(i===undefined||i.data===undefined||i.data.length===0)return;var s=i.data[0],o=n.getToolState(e,r),u;o===undefined||o.data.length===0?(u={intervalId:undefined,framesPerSecond:t,lastFrameTimeStamp:undefined,frameRate:0},n.addToolState(e,r,u)):(u=o.data[0],u.framesPerSecond=t);if(u.intervalId!==undefined)return;u.intervalId=setInterval(function(){var t=s.stacks[s.currentStackIndex].currentImageIdIndex,r=s.currentStackIndex;u.framesPerSecond>0?n.incrementTimePoint(e,1,!0):n.incrementTimePoint(e,-1,!0)},1e3/Math.abs(u.framesPerSecond))}function s(e){var t=n.getToolState(e,r),i;if(t===undefined||t.data.length===0)return;i=t.data[0],clearInterval(i.intervalId),i.intervalId=undefined}n===undefined&&(n={});var r="timeSeriesPlayer";return n.timeSeriesPlayer={start:i,stop:s},n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function i(t,n){e(n.element).off("CornerstoneToolsMouseDrag",o),e(n.element).off("CornerstoneToolsMouseUp",i)}function s(t,r){if(n.isMouseButtonEnabled(r.which,t.data.mouseButtonMask)){var s={deltaY:0,options:t.data.options};return e(r.element).on("CornerstoneToolsMouseDrag",s,o),e(r.element).on("CornerstoneToolsMouseUp",i),t.stopImmediatePropagation(),!1}}function o(t,r){t.data.deltaY+=r.deltaPoints.page.y;var i=n.getToolState(r.element,"timeSeries");if(i===undefined||i.data===undefined||i.data.length===0)return;var s=i.data[0],o=e(r.element).height()/s.stacks.length;t.data.options!==undefined&&t.data.options.timeSeriesScrollSpeed!==undefined&&(o=t.data.options.timeSeriesScrollSpeed);if(t.data.deltaY>=o||t.data.deltaY<=-o){var u=Math.round(t.data.deltaY/o),a=t.data.deltaY%o;n.incrementTimePoint(r.element,u),t.data.deltaY=a}return!1}function u(e,t){var r=-t.direction;n.incrementTimePoint(t.element,r)}function a(e){var t=e.originalEvent.detail,r={deltaY:0};r.deltaY+=t.deltaPoints.page.y;var i=n.getToolState(t.element,"stack");if(i===undefined||i.data===undefined||i.data.length===0)return;if(r.deltaY>=3||r.deltaY<=-3){var s=r.deltaY/3,o=r.deltaY%3;n.setTimePoint(r.element,s),r.deltaY=o}return!1}n===undefined&&(n={});var r="timeSeriesScroll";return n.timeSeriesScroll=n.simpleMouseButtonTool(s),n.timeSeriesScrollWheel=n.mouseWheelTool(u),n.timeSeriesScrollTouchDrag=n.touchDragTool(a),n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function r(e,t){var n=Math.pow(10,t);return Math.round(e*n)/n}return n===undefined&&(n={}),n.roundToDecimal=r,n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n,r){"use strict";function i(e){var t=n.point.copy(e.page),r=n.point.copy(e.image);return{page:t,image:r}}return r===undefined&&(r={}),r.copyPoints=i,r}($,cornerstone,cornerstoneMath,cornerstoneTools),cornerstoneTools=function(e){"use strict";function t(e,t,n,r,i){var s=.5522848,o=r/2*s,u=i/2*s,a=t+r,f=n+i,l=t+r/2,c=n+i/2;e.beginPath(),e.moveTo(t,c),e.bezierCurveTo(t,c-u,l-o,n,l,n),e.bezierCurveTo(l+o,n,a,c-u,a,c),e.bezierCurveTo(a,c+u,l+o,f,l,f),e.bezierCurveTo(l-o,f,t,c+u,t,c),e.closePath(),e.stroke()}return e===undefined&&(e={}),e.drawEllipse=t,e}(cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function r(e,t){var n=1<<e-1;return(t&n)!==0}return n===undefined&&(n={}),n.isMouseButtonEnabled=r,n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function r(e){return e.stopPropagation&&e.stopPropagation(),e.preventDefault&&e.preventDefault(),e.cancelBubble=!0,e.returnValue=!1,!1}return n===undefined&&(n={}),n.pauseEvent=r,n}($,cornerstone,cornerstoneTools),cornerstoneTools=function(e,t,n){"use strict";function r(e,t){var n=e.clone().sub(t.imagePositionPatient),r=t.columnCosines.dot(n)/t.columnPixelSpacing,i=t.rowCosines.dot(n)/t.rowPixelSpacing,s={x:r,y:i};return s}function i(e,t){var n=t.columnCosines.clone().multiplyScalar(e.x);n.multiplyScalar(t.columnPixelSpacing);var r=t.rowCosines.clone().multiplyScalar(e.y);r.multiplyScalar(t.rowPixelSpacing);var i=n.add(r);return i.add(t.imagePositionPatient),i}return n===undefined&&(n={}),n.referenceLines===undefined&&(n.referenceLines={}),n.projectPatientPointToImagePlane=r,n.imagePointToPatientPoint=i,n}($,cornerstone,cornerstoneTools),cornerstone=function(e){"use strict";function t(t,n,r){var i=.1;e.setToPixelCoordinateSystem(t,n,i);var s=r/t.viewport.scale/i,o=r/t.viewport.scale/i;return{fontSize:s,lineHeight:o,fontScale:i}}return e===undefined&&(e={}),cornerstoneTools.setContextToDisplayFontSize=t,e}(cornerstone);define("cornerstoneTools",function(){}),function(e,t){typeof module!="undefined"&&module.exports?module.exports=t():typeof define=="function"&&define.amd?define("dicomParser",[],t):(dicomParser===undefined&&(dicomParser={},typeof Package!="undefined"&&(e.dicomParser=dicomParser)),dicomParser=t())}(this,function(){function e(e,t){function r(){n.seek(128);var e=n.readFixedString(4);if(e!=="DICM")throw"dicomParser.parseDicom: DICM prefix not found at location 132"}function i(){r();var e=[],t={};while(n.position<n.byteArray.length){var i=n.position,s=dicomParser.readDicomElementExplicit(n,e);if(s.tag>"x0002ffff"){n.position=i;break}s.parser=dicomParser.littleEndianByteArrayParser,t[s.tag]=s}var o=new dicomParser.DataSet(n.byteArrayParser,n.byteArray,t);return o.warnings=n.warnings,o}function s(e){if(e.elements.x00020010===undefined)throw"dicomParser.parseDicom: missing required meta header attribute 0002,0010";var t=e.elements.x00020010;return dicomParser.readFixedString(n.byteArray,t.dataOffset,t.length)}function o(e){return e==="1.2.840.10008.1.2"?!1:!0}function u(t){return t==="1.2.840.10008.1.2.2"?new dicomParser.ByteStream(dicomParser.bigEndianByteArrayParser,e,n.position):new dicomParser.ByteStream(dicomParser.littleEndianByteArrayParser,e,n.position)}function a(e,t){for(var n in e.elements)e.elements.hasOwnProperty(n)&&(t.elements[n]=e.elements[n]);return e.warnings!==undefined&&(t.warnings=e.warnings.concat(t.warnings)),t}function f(e){var n=s(e),r=o(n),i=u(n),a={},f=new dicomParser.DataSet(i.byteArrayParser,i.byteArray,a);f.warnings=i.warnings;try{r?dicomParser.parseDicomDataSetExplicit(f,i,i.byteArray.length,t):dicomParser.parseDicomDataSetImplicit(f,i,i.byteArray.length,t)}catch(l){var c={exception:l,dataSet:f};throw c}return f}function l(){var e=i(),t=f(e);return a(e,t)}if(e===undefined)throw"dicomParser.parseDicom: missing required parameter 'byteArray'";var n=new dicomParser.ByteStream(dicomParser.littleEndianByteArrayParser,e);return l()}return dicomParser===undefined?{parseDicom:e}:(dicomParser.parseDicom=e,dicomParser)});var dicomParser=function(e){"use strict";return e===undefined&&(e={}),e.bigEndianByteArrayParser={readUint16:function(e,t){if(t<0)throw"bigEndianByteArrayParser.readUint16: position cannot be less than 0";if(t+2>e.length)throw"bigEndianByteArrayParser.readUint16: attempt to read past end of buffer";return(e[t]<<8)+e[t+1]},readInt16:function(e,t){if(t<0)throw"bigEndianByteArrayParser.readInt16: position cannot be less than 0";if(t+2>e.length)throw"bigEndianByteArrayParser.readInt16: attempt to read past end of buffer";var n=(e[t]<<8)+e[t+1];return n&32768&&(n=n-65535-1),n},readUint32:function(e,t){if(t<0)throw"bigEndianByteArrayParser.readUint32: position cannot be less than 0";if(t+4>e.length)throw"bigEndianByteArrayParser.readUint32: attempt to read past end of buffer";var n=256*(256*(256*e[t]+e[t+1])+e[t+2])+e[t+3];return n},readInt32:function(e,t){if(t<0)throw"bigEndianByteArrayParser.readInt32: position cannot be less than 0";if(t+4>e.length)throw"bigEndianByteArrayParser.readInt32: attempt to read past end of buffer";var n=(e[t]<<24)+(e[t+1]<<16)+(e[t+2]<<8)+e[t+3];return n},readFloat:function(e,t){if(t<0)throw"bigEndianByteArrayParser.readFloat: position cannot be less than 0";if(t+4>e.length)throw"bigEndianByteArrayParser.readFloat: attempt to read past end of buffer";var n=new Uint8Array(4);n[3]=e[t],n[2]=e[t+1],n[1]=e[t+2],n[0]=e[t+3];var r=new Float32Array(n.buffer);return r[0]},readDouble:function(e,t){if(t<0)throw"bigEndianByteArrayParser.readDouble: position cannot be less than 0";if(t+8>e.length)throw"bigEndianByteArrayParser.readDouble: attempt to read past end of buffer";var n=new Uint8Array(8);n[7]=e[t],n[6]=e[t+1],n[5]=e[t+2],n[4]=e[t+3],n[3]=e[t+4],n[2]=e[t+5],n[1]=e[t+6],n[0]=e[t+7];var r=new Float64Array(n.buffer);return r[0]}},e}(dicomParser),dicomParser=function(e){"use strict";return e===undefined&&(e={}),e.readFixedString=function(e,t,n){if(n<0)throw"readFixedString - length cannot be less than 0";if(t+n>e.length)throw"dicomParser.readFixedString: attempt to read past end of buffer";var r="";for(var i=0;i<n;i++){var s=e[t+i];if(s===0)return t+=n,r;r+=String.fromCharCode(s)}return r},e}(dicomParser),dicomParser=function(e){"use strict";return e===undefined&&(e={}),e.ByteStream=function(e,t,n){if(e===undefined)throw"dicomParser.ByteStream: missing required parameter 'byteArrayParser'";if(t===undefined)throw"dicomParser.ByteStream: missing required parameter 'byteArray'";if(t instanceof Uint8Array==0)throw"dicomParser.ByteStream: parameter byteArray is not of type Uint8Array";if(n<0)throw"dicomParser.ByteStream: parameter 'position' cannot be less than 0";if(n>=t.length)throw"dicomParser.ByteStream: parameter 'position' cannot be greater than or equal to 'byteArray' length";this.byteArrayParser=e,this.byteArray=t,this.position=n?n:0,this.warnings=[]},e.ByteStream.prototype.seek=function(e){if(this.position+e<0)throw"cannot seek to position < 0";this.position+=e},e.ByteStream.prototype.readByteStream=function(t){if(this.position+t>this.byteArray.length)throw"readByteStream - buffer overread";var n=new Uint8Array(this.byteArray.buffer,this.position,t);return this.position+=t,new e.ByteStream(this.byteArrayParser,n)},e.ByteStream.prototype.readUint16=function(){var e=this.byteArrayParser.readUint16(this.byteArray,this.position);return this.position+=2,e},e.ByteStream.prototype.readUint32=function(){var e=this.byteArrayParser.readUint32(this.byteArray,this.position);return this.position+=4,e},e.ByteStream.prototype.readFixedString=function(t){var n=e.readFixedString(this.byteArray,this.position,t);return this.position+=t,n},e}(dicomParser),dicomParser=function(e){"use strict";function t(e,t){return e.parser!==undefined?e.parser:t}return e===undefined&&(e={}),e.DataSet=function(e,t,n){this.byteArrayParser=e,this.byteArray=t,this.elements=n},e.DataSet.prototype.uint16=function(e,n){var r=this.elements[e];return n=n!==undefined?n:0,r&&r.length!==0?t(r,this.byteArrayParser).readUint16(this.byteArray,r.dataOffset+n*2):undefined},e.DataSet.prototype.int16=function(e,n){var r=this.elements[e];return n=n!==undefined?n:0,r&&r.length!==0?t(r,this.byteArrayParser).readInt16(this.byteArray,r.dataOffset+n*2):undefined},e.DataSet.prototype.uint32=function(e,n){var r=this.elements[e];return n=n!==undefined?n:0,r&&r.length!==0?t(r,this.byteArrayParser).readUint32(this.byteArray,r.dataOffset+n*4):undefined},e.DataSet.prototype.int32=function(e,n){var r=this.elements[e];return n=n!==undefined?n:0,r&&r.length!==0?t(r,this.byteArrayParser).readInt32(this.byteArray,r.dataOffset+n*4):undefined},e.DataSet.prototype.float=function(e,n){var r=this.elements[e];return n=n!==undefined?n:0,r&&r.length!==0?t(r,this.byteArrayParser).readFloat(this.byteArray,r.dataOffset+n*4):undefined},e.DataSet.prototype.double=function(e,n){var r=this.elements[e];return n=n!==undefined?n:0,r&&r.length!==0?t(r,this.byteArrayParser).readDouble(this.byteArray,r.dataOffset+n*8):undefined},e.DataSet.prototype.numStringValues=function(t){var n=this.elements[t];if(n&&n.length>0){var r=e.readFixedString(this.byteArray,n.dataOffset,n.length),i=r.match(/\\/g);return i===null?1:i.length+1}return undefined},e.DataSet.prototype.string=function(t,n){var r=this.elements[t];if(r&&r.length>0){var i=e.readFixedString(this.byteArray,r.dataOffset,r.length);if(n>=0){var s=i.split("\\");return s[n].trim()}return i.trim()}return undefined},e.DataSet.prototype.text=function(t,n){var r=this.elements[t];if(r&&r.length>0){var i=e.readFixedString(this.byteArray,r.dataOffset,r.length);if(n>=0){var s=i.split("\\");return s[n].replace(/ +$/,"")}return i.replace(/ +$/,"")}return undefined},e.DataSet.prototype.floatString=function(e,t){var n=this.elements[e];if(n&&n.length>0){t=t!==undefined?t:0;var r=this.string(e,t);if(r!==undefined)return parseFloat(r)}return undefined},e.DataSet.prototype.intString=function(e,t){var n=this.elements[e];if(n&&n.length>0){t=t!==undefined?t:0;var r=this.string(e,t);if(r!==undefined)return parseInt(r)}return undefined},e}(dicomParser),dicomParser=function(e){"use strict";return e===undefined&&(e={}),e.findEndOfEncapsulatedElement=function(t,n,r){if(t===undefined)throw"dicomParser.findEndOfEncapsulatedElement: missing required parameter 'byteStream'";if(n===undefined)throw"dicomParser.findEndOfEncapsulatedElement: missing required parameter 'element'";n.encapsulatedPixelData=!0,n.basicOffsetTable=[],n.fragments=[];var i=e.readTag(t);if(i!=="xfffee000")throw"dicomParser.findEndOfEncapsulatedElement: basic offset table not found";var s=t.readUint32(),o=s/4;for(var u=0;u<o;u++){var a=t.readUint32();n.basicOffsetTable.push(a)}var f=t.position;while(t.position<t.byteArray.length){var l=e.readTag(t),c=t.readUint32();if(l==="xfffee0dd"){t.seek(c),n.length=t.position-n.dataOffset;return}if(l!=="xfffee000"){r&&r.push("unexpected tag "+l+" while searching for end of pixel data element with undefined length"),c>t.byteArray.length-t.position&&(c=t.byteArray.length-t.position),n.fragments.push({offset:t.position-f-8,position:t.position,length:c}),t.seek(c),n.length=t.position-n.dataOffset;return}n.fragments.push({offset:t.position-f-8,position:t.position,length:c}),t.seek(c)}r&&r.push("pixel data element "+n.tag+" missing sequence delimiter tag xfffee0dd")},e}(dicomParser),dicomParser=function(e){"use strict";return e===undefined&&(e={}),e.findItemDelimitationItemAndSetElementLength=function(e,t){if(e===undefined)throw"dicomParser.readDicomElementImplicit: missing required parameter 'byteStream'";var n=8,r=e.byteArray.length-n;while(e.position<=r){var i=e.readUint16();if(i===65534){var s=e.readUint16();if(s===57357){var o=e.readUint32();o!==0&&e.warnings("encountered non zero length following item delimiter at position"+e.position-4+" while reading element of undefined length with tag ' + element.tag"),t.length=e.position-t.dataOffset;return}}}t.length=e.byteArray.length-t.dataOffset,e.seek(e.byteArray.length-e.position)},e}(dicomParser),dicomParser=function(e){"use strict";return e===undefined&&(e={}),e.littleEndianByteArrayParser={readUint16:function(e,t){if(t<0)throw"littleEndianByteArrayParser.readUint16: position cannot be less than 0";if(t+2>e.length)throw"littleEndianByteArrayParser.readUint16: attempt to read past end of buffer";return e[t]+e[t+1]*256},readInt16:function(e,t){if(t<0)throw"littleEndianByteArrayParser.readInt16: position cannot be less than 0";if(t+2>e.length)throw"littleEndianByteArrayParser.readInt16: attempt to read past end of buffer";var n=e[t]+(e[t+1]<<8);return n&32768&&(n=n-65535-1),n},readUint32:function(e,t){if(t<0)throw"littleEndianByteArrayParser.readUint32: position cannot be less than 0";if(t+4>e.length)throw"littleEndianByteArrayParser.readUint32: attempt to read past end of buffer";var n=e[t]+e[t+1]*256+e[t+2]*256*256+e[t+3]*256*256*256;return n},readInt32:function(e,t){if(t<0)throw"littleEndianByteArrayParser.readInt32: position cannot be less than 0";if(t+4>e.length)throw"littleEndianByteArrayParser.readInt32: attempt to read past end of buffer";var n=e[t]+(e[t+1]<<8)+(e[t+2]<<16)+(e[t+3]<<24);return n},readFloat:function(e,t){if(t<0)throw"littleEndianByteArrayParser.readFloat: position cannot be less than 0";if(t+4>e.length)throw"littleEndianByteArrayParser.readFloat: attempt to read past end of buffer";var n=new Uint8Array(4);n[0]=e[t],n[1]=e[t+1],n[2]=e[t+2],n[3]=e[t+3];var r=new Float32Array(n.buffer);return r[0]},readDouble:function(e,t){if(t<0)throw"littleEndianByteArrayParser.readDouble: position cannot be less than 0";if(t+8>e.length)throw"littleEndianByteArrayParser.readDouble: attempt to read past end of buffer";var n=new Uint8Array(8);n[0]=e[t],n[1]=e[t+1],n[2]=e[t+2],n[3]=e[t+3],n[4]=e[t+4],n[5]=e[t+5],n[6]=e[t+6],n[7]=e[t+7];var r=new Float64Array(n.buffer);return r[0]}},e}(dicomParser),dicomParser=function(e){"use strict";return e===undefined&&(e={}),e.parseDicomDataSetExplicit=function(t,n,r,i){r=r===undefined?n.byteArray.length:r,i=i||{};if(n===undefined)throw"dicomParser.parseDicomDataSetExplicit: missing required parameter 'byteStream'";if(r<n.position||r>n.byteArray.length)throw"dicomParser.parseDicomDataSetExplicit: invalid value for parameter 'maxPosition'";var s=t.elements;while(n.position<r){var o=e.readDicomElementExplicit(n,t.warnings,i.untilTag);s[o.tag]=o;if(o.tag===i.untilTag)return}},e.parseDicomDataSetImplicit=function(t,n,r,i){r=r===undefined?t.byteArray.length:r,i=i||{};if(n===undefined)throw"dicomParser.parseDicomDataSetImplicit: missing required parameter 'byteStream'";if(r<n.position||r>n.byteArray.length)throw"dicomParser.parseDicomDataSetImplicit: invalid value for parameter 'maxPosition'";var s=t.elements;while(n.position<r){var o=e.readDicomElementImplicit(n,i.untilTag);s[o.tag]=o;if(o.tag===i.untilTag)return}},e}(dicomParser),dicomParser=function(e){"use strict";function t(e){return e==="OB"||e==="OW"||e==="SQ"||e==="OF"||e==="UT"||e==="UN"?4:2}return e===undefined&&(e={}),e.readDicomElementExplicit=function(n,r,i){if(n===undefined)throw"dicomParser.readDicomElementExplicit: missing required parameter 'byteStream'";var s={tag:e.readTag(n),vr:n.readFixedString(2)},o=t(s.vr);return o===2?(s.length=n.readUint16(),s.dataOffset=n.position):(n.seek(2),s.length=n.readUint32(),s.dataOffset=n.position),s.length===4294967295&&(s.hadUndefinedLength=!0),s.tag===i?s:s.vr==="SQ"?(e.readSequenceItemsExplicit(n,s,r),s):s.length===4294967295?s.tag==="x7fe00010"?(e.findEndOfEncapsulatedElement(n,s,r),s):(e.findItemDelimitationItemAndSetElementLength(n,s),s):(n.seek(s.length),s)},e}(dicomParser),dicomParser=function(e){"use strict";return e===undefined&&(e={}),e.readDicomElementImplicit=function(t,n){if(t===undefined)throw"dicomParser.readDicomElementImplicit: missing required parameter 'byteStream'";var r={tag:e.readTag(t),length:t.readUint32(),dataOffset:t.position};r.length===4294967295&&(r.hadUndefinedLength=!0);if(r.tag===n)return r;if(t.position+4<=t.byteArray.length){var i=e.readTag(t);t.seek(-4);if(i==="xfffee000")return e.readSequenceItemsImplicit(t,r),r}return r.length===4294967295?(e.findItemDelimitationItemAndSetElementLength(t,r),r):(t.seek(r.length),r)},e}(dicomParser),dicomParser=function(e){"use strict";function t(e,t,n){if(t.length===1)return new Uint8Array(e.byteArray.buffer,t[0].dataOffset,t[0].length);var r=new Uint8Array(n),i=0;for(var s=0;s<t.length;s++){var o=t[s].dataOffset;for(var u=0;u<t[s].length;u++)r[i++]=e.byteArray[o++]}return r}function n(n,r){var i=[],s=0;while(n.position<r&&n.position<n.length){var o=e.readSequenceItem(n);if(o.tag==="xfffee0dd")break;i.push(o),n.seek(o.length),s+=o.length}var u=t(n,i,s);return u}function r(e,t,r){var i=e.basicOffsetTable.length;if(r>i)throw"dicomParser.readEncapsulatedPixelData: parameter frame exceeds number of frames in basic offset table";var s=e.basicOffsetTable[r];t.seek(s);var o=e.basicOffsetTable[r+1];o===undefined&&(o=t.position+e.length);var u=n(t,o);return u}function i(e,t,r){if(r!==0)throw"dicomParser.readEncapsulatedPixelData: non zero frame specified for single frame encapsulated pixel data";var i=t.position+e.length,s=n(t,i);return s}return e===undefined&&(e={}),e.readEncapsulatedPixelData=function(t,n,s){if(t===undefined)throw"dicomParser.readEncapsulatedPixelData: missing required parameter 'dataSet'";if(n===undefined)throw"dicomParser.readEncapsulatedPixelData: missing required parameter 'element'";if(s===undefined)throw"dicomParser.readEncapsulatedPixelData: missing required parameter 'frame'";if(n.tag!=="x7fe00010")throw"dicomParser.readEncapsulatedPixelData: parameter 'element' refers to non pixel data tag (expected tag = x7fe00010'";if(n.encapsulatedPixelData!==!0)throw"dicomParser.readEncapsulatedPixelData: parameter 'element' refers to pixel data element that does not have encapsulated pixel data";if(n.hadUndefinedLength!==!0)throw"dicomParser.readEncapsulatedPixelData: parameter 'element' refers to pixel data element that does not have encapsulated pixel data";if(n.basicOffsetTable===undefined)throw"dicomParser.readEncapsulatedPixelData: parameter 'element' refers to pixel data element that does not have encapsulated pixel data";if(n.fragments===undefined)throw"dicomParser.readEncapsulatedPixelData: parameter 'element' refers to pixel data element that does not have encapsulated pixel data";if(s<0)throw"dicomParser.readEncapsulatedPixelData: parameter 'frame' must be >= 0";var o=new e.ByteStream(t.byteArrayParser,t.byteArray,n.dataOffset),u=e.readSequenceItem(o);if(u.tag!=="xfffee000")throw"dicomParser.readEncapsulatedPixelData: missing basic offset table xfffee000";return o.seek(u.length),n.basicOffsetTable.length!==0?r(n,o,s):i(n,o,s)},e}(dicomParser),dicomParser=function(e){"use strict";function t(t,n){var r={};while(t.position<t.byteArray.length){var i=e.readDicomElementExplicit(t,n);r[i.tag]=i;if(i.tag==="xfffee00d")return new e.DataSet(t.byteArrayParser,t.byteArray,r)}return t.warnings.push("eof encountered before finding sequence delimitation item while reading sequence item of undefined length"),new e.DataSet(t.byteArrayParser,t.byteArray,r)}function n(n,r){var i=e.readSequenceItem(n);return i.length===4294967295?(i.hadUndefinedLength=!0,i.dataSet=t(n,r),i.length=n.position-i.dataOffset):(i.dataSet=new e.DataSet(n.byteArrayParser,n.byteArray,{}),e.parseDicomDataSetExplicit(i.dataSet,n,n.position+i.length)),i}function r(e,t,r){while(e.position<e.byteArray.length){var i=n(e,r);t.items.push(i);if(i.tag==="xfffee0dd"){t.length=e.position-t.dataOffset;return}}e.warnings.push("eof encountered before finding sequence delimitation item in sequence element of undefined length with tag "+t.tag),t.length=e.byteArray.length-t.dataOffset}function i(e,t,r){var i=t.dataOffset+t.length;while(e.position<i){var s=n(e,r);t.items.push(s)}}return e===undefined&&(e={}),e.readSequenceItemsExplicit=function(e,t,n){if(e===undefined)throw"dicomParser.readSequenceItemsExplicit: missing required parameter 'byteStream'";if(t===undefined)throw"dicomParser.readSequenceItemsExplicit: missing required parameter 'element'";t.items=[],t.length===4294967295?r(e,t):i(e,t,n)},e}(dicomParser),dicomParser=function(e){"use strict";function t(t){var n={};while(t.position<t.byteArray.length){var r=e.readDicomElementImplicit(t);n[r.tag]=r;if(r.tag==="xfffee00d")return new e.DataSet(t.byteArrayParser,t.byteArray,n)}return t.warnings.push("eof encountered before finding sequence item delimiter in sequence item of undefined length"),new e.DataSet(t.byteArrayParser,t.byteArray,n)}function n(n){var r=e.readSequenceItem(n);return r.length===4294967295?(r.hadUndefinedLength=!0,r.dataSet=t(n),r.length=n.position-r.dataOffset):(r.dataSet=new e.DataSet(n.byteArrayParser,n.byteArray,{}),e.parseDicomDataSetImplicit(r.dataSet,n,n.position+r.length)),r}function r(e,t){while(e.position<e.byteArray.length){var r=n(e);t.items.push(r);if(r.tag==="xfffee0dd"){t.length=e.position-t.dataOffset;return}}e.warnings.push("eof encountered before finding sequence delimitation item in sequence of undefined length"),t.length=e.byteArray.length-t.dataOffset}function i(e,t){var r=t.dataOffset+t.length;while(e.position<r){var i=n(e);t.items.push(i)}}return e===undefined&&(e={}),e.readSequenceItemsImplicit=function(e,t){if(e===undefined)throw"dicomParser.readSequenceItemsImplicit: missing required parameter 'byteStream'";if(t===undefined)throw"dicomParser.readSequenceItemsImplicit: missing required parameter 'element'";t.items=[],t.length===4294967295?r(e,t):i(e,t)},e}(dicomParser),dicomParser=function(e){"use strict";return e===undefined&&(e={}),e.readSequenceItem=function(t){if(t===undefined)throw"dicomParser.readSequenceItem: missing required parameter 'byteStream'";var n={tag:e.readTag(t),length:t.readUint32(),dataOffset:t.position};return n},e}(dicomParser),dicomParser=function(e){"use strict";return e===undefined&&(e={}),e.readTag=function(e){if(e===undefined)throw"dicomParser.readTag: missing required parameter 'byteStream'";var t=e.readUint16()*256*256,n=e.readUint16(),r="x"+("00000000"+(t+n).toString(16)).substr(-8);return r},e}(dicomParser),dicomParser=function(e){"use strict";return e===undefined&&(e={}),e.explicitDataSetToJS=function(t,n){if(t===undefined)throw"dicomParser.explicitDataSetToJS: missing required parameter dataSet";n=n||{omitPrivateAttibutes:!0,maxElementLength:128};var r={};for(var i in t.elements){var s=t.elements[i];if(n.omitPrivateAttibutes===!0&&e.isPrivateTag(i))continue;if(s.items){var o=[];for(var u=0;u<s.items.length;u++)o.push(e.explicitDataSetToJS(s.items[u].dataSet,n));r[i]=o}else{var a;a=undefined,s.length<n.maxElementLength&&(a=e.explicitElementToString(t,s)),a!==undefined?r[i]=a:r[i]={dataOffset:s.dataOffset,length:s.length}}}return r},e}(dicomParser),dicomParser=function(e){"use strict";return e===undefined&&(e={}),e.explicitElementToString=function(t,n){function o(e,n){var r="";for(var s=0;s<e;s++)s!==0&&(r+="/"),r+=n.call(t,i).toString();return r}if(t===undefined||n===undefined)throw"dicomParser.explicitElementToString: missing required parameters";if(n.vr===undefined)throw"dicomParser.explicitElementToString: cannot convert implicit element to string";var r=n.vr,i=n.tag,s;if(e.isStringVr(r)===!0)s=t.string(i);else{if(r=="AT"){var u=t.uint32(i);return u===undefined?undefined:(u<0&&(u=4294967295+u+1),"x"+u.toString(16).toUpperCase())}r=="US"?s=o(n.length/2,t.uint16):r==="SS"?s=o(n.length/2,t.int16):r=="UL"?s=o(n.length/4,t.uint32):r==="SL"?s=o(n.length/4,t.int32):r=="FD"?s=o(n.length/8,t.int32):r=="FL"&&(s=o(n.length/4,t.float))}return s},e}(dicomParser),dicomParser=function(e){"use strict";e===undefined&&(e={});var t={AE:!0,AS:!0,AT:!1,CS:!0,DA:!0,DS:!0,DT:!0,FL:!1,FD:!1,IS:!0,LO:!0,LT:!0,OB:!1,OD:!1,OF:!1,OW:!1,PN:!0,SH:!0,SL:!1,SQ:!1,SS:!1,ST:!0,TM:!0,UI:!0,UL:!1,UN:undefined,UR:!0,US:!1,UT:!0};return e.isStringVr=function(e){return t[e]},e.isPrivateTag=function(e){var t=parseInt(e[4]),n=t%2===1;return n},e.parsePN=function(e){if(e===undefined)return undefined;var t=e.split("^");return{familyName:t[0],givenName:t[1],middleName:t[2],prefix:t[3],suffix:t[4]}},e.parseDA=function(e){if(e&&e.length===8){var t=parseInt(e.substring(0,4),10),n=parseInt(e.substring(4,6),10),r=parseInt(e.substring(6,8),10);return{year:t,month:n,day:r}}return undefined},e.parseTM=function(e){if(e.length>=2){var t=parseInt(e.substring(0,2),10),n=e.length>=4?parseInt(e.substring(2,4),10):undefined,r=e.length>=6?parseInt(e.substring(4,6),10):undefined,i=e.length>=8?parseInt(e.substring(7,13),10):undefined;return{hours:t,minutes:n,seconds:r,fractionalSeconds:i}}return undefined},e}(dicomParser);(function(e,t){"use strict";function i(e,i){function u(){var t=a(),n=t.data,r=e.naturalHeight*e.naturalWidth,i=new Uint8Array(r*4),s=0,o=0;for(var u=0;u<r;u++)i[o++]=n[s++],i[o++]=n[s++],i[o++]=n[s++],i[o++]=255,s++;return i}function a(){var t;r!==i?(n.height=e.naturalHeight,n.width=e.naturalWidth,t=n.getContext("2d"),t.drawImage(e,0,0)):t=n.getContext("2d");var s=t.getImageData(0,0,e.naturalWidth,e.naturalHeight);return s}function f(){if(r===i)return n;n.height=e.naturalHeight,n.width=e.naturalWidth;var t=n.getContext("2d");return t.drawImage(e,0,0),r=i,n}function l(){return e}var s=e.naturalHeight,o=e.naturalWidth,c={imageId:i,minPixelValue:0,maxPixelValue:255,slope:1,intercept:0,windowCenter:127,windowWidth:256,render:t.renderColorImage,getPixelData:u,getImageData:a,getCanvas:f,getImage:l,rows:s,columns:o,height:s,width:o,color:!0,columnPixelSpacing:1,rowPixelSpacing:1,invert:!1,sizeInBytes:s*o*4};return c}function s(t){var n=e.Deferred(),r=new Image;return r.crossOrigin="anonymous",r.onload=function(){var e=i(r,t);n.resolve(e)},r.onerror=function(){n.reject()},r.src=t,n}var n=document.createElement("canvas"),r="";return t.registerImageLoader("http",s),t.registerImageLoader("https",s),t})($,cornerstone),define("cornerstoneWebImageLoader",function(){});var JpxImage=function(){function n(){this.failOnCorruptedImage=!1}function r(e,t){e.x0=Math.ceil(t.XOsiz/e.XRsiz),e.x1=Math.ceil(t.Xsiz/e.XRsiz),e.y0=Math.ceil(t.YOsiz/e.YRsiz),e.y1=Math.ceil(t.Ysiz/e.YRsiz),e.width=e.x1-e.x0,e.height=e.y1-e.y0}function i(e,t){var n=e.SIZ,r,i=[],s=Math.ceil((n.Xsiz-n.XTOsiz)/n.XTsiz),o=Math.ceil((n.Ysiz-n.YTOsiz)/n.YTsiz);for(var u=0;u<o;u++)for(var a=0;a<s;a++)r={},r.tx0=Math.max(n.XTOsiz+a*n.XTsiz,n.XOsiz),r.ty0=Math.max(n.YTOsiz+u*n.YTsiz,n.YOsiz),r.tx1=Math.min(n.XTOsiz+(a+1)*n.XTsiz,n.Xsiz),r.ty1=Math.min(n.YTOsiz+(u+1)*n.YTsiz,n.Ysiz),r.width=r.tx1-r.tx0,r.height=r.ty1-r.ty0,r.components=[],i.push(r);e.tiles=i;var f=n.Csiz;for(var l=0,c=f;l<c;l++){var h=t[l];for(var p=0,d=i.length;p<d;p++){var v={};r=i[p],v.tcx0=Math.ceil(r.tx0/h.XRsiz),v.tcy0=Math.ceil(r.ty0/h.YRsiz),v.tcx1=Math.ceil(r.tx1/h.XRsiz),v.tcy1=Math.ceil(r.ty1/h.YRsiz),v.width=v.tcx1-v.tcx0,v.height=v.tcy1-v.tcy0,r.components[l]=v}}}function s(e,t,n){var r=t.codingStyleParameters,i={};return r.entropyCoderWithCustomPrecincts?(i.PPx=r.precinctsSizes[n].PPx,i.PPy=r.precinctsSizes[n].PPy):(i.PPx=15,i.PPy=15),i.xcb_=n>0?Math.min(r.xcb,i.PPx-1):Math.min(r.xcb,i.PPx),i.ycb_=n>0?Math.min(r.ycb,i.PPy-1):Math.min(r.ycb,i.PPy),i}function o(e,t,n){var r=1<<n.PPx,i=1<<n.PPy,s=t.resLevel===0,o=1<<n.PPx+(s?0:-1),u=1<<n.PPy+(s?0:-1),a=t.trx1>t.trx0?Math.ceil(t.trx1/r)-Math.floor(t.trx0/r):0,f=t.try1>t.try0?Math.ceil(t.try1/i)-Math.floor(t.try0/i):0,l=a*f;t.precinctParameters={precinctWidth:r,precinctHeight:i,numprecinctswide:a,numprecinctshigh:f,numprecincts:l,precinctWidthInSubband:o,precinctHeightInSubband:u}}function u(e,t,n){var r=n.xcb_,i=n.ycb_,s=1<<r,o=1<<i,u=t.tbx0>>r,a=t.tby0>>i,f=t.tbx1+s-1>>r,l=t.tby1+o-1>>i,c=t.resolution.precinctParameters,h=[],p=[],d,v,m,g;for(v=a;v<l;v++)for(d=u;d<f;d++){m={cbx:d,cby:v,tbx0:s*d,tby0:o*v,tbx1:s*(d+1),tby1:o*(v+1)},m.tbx0_=Math.max(t.tbx0,m.tbx0),m.tby0_=Math.max(t.tby0,m.tby0),m.tbx1_=Math.min(t.tbx1,m.tbx1),m.tby1_=Math.min(t.tby1,m.tby1);var y=Math.floor((m.tbx0_-t.tbx0)/c.precinctWidthInSubband),b=Math.floor((m.tby0_-t.tby0)/c.precinctHeightInSubband);g=y+b*c.numprecinctswide,m.precinctNumber=g,m.subbandType=t.type,m.Lblock=3;if(m.tbx1_<=m.tbx0_||m.tby1_<=m.tby0_)continue;h.push(m);var w=p[g];w!==undefined?(d<w.cbxMin?w.cbxMin=d:d>w.cbxMax&&(w.cbxMax=d),v<w.cbyMin?w.cbxMin=v:v>w.cbyMax&&(w.cbyMax=v)):p[g]=w={cbxMin:d,cbyMin:v,cbxMax:d,cbyMax:v},m.precinct=w}t.codeblockParameters={codeblockWidth:r,codeblockHeight:i,numcodeblockwide:f-u+1,numcodeblockhigh:l-a+1},t.codeblocks=h,t.precincts=p}function a(e,t,n){var r=[],i=e.subbands;for(var s=0,o=i.length;s<o;s++){var u=i[s],a=u.codeblocks;for(var f=0,l=a.length;f<l;f++){var c=a[f];if(c.precinctNumber!==t)continue;r.push(c)}}return{layerNumber:n,codeblocks:r}}function f(e){var t=e.SIZ,n=e.currentTile.index,r=e.tiles[n],i=r.codingStyleDefaultParameters.layersCount,s=t.Csiz,o=0;for(var u=0;u<s;u++)o=Math.max(o,r.components[u].codingStyleParameters.decompositionLevelsCount);var f=0,l=0,c=0,h=0;this.nextPacket=function(){for(;f<i;f++){for(;l<=o;l++){for(;c<s;c++){var t=r.components[c];if(l>t.codingStyleParameters.decompositionLevelsCount)continue;var n=t.resolutions[l],u=n.precinctParameters.numprecincts;for(;h<u;){var p=a(n,h,f);return h++,p}h=0}c=0}l=0}}}function l(e){var t=e.SIZ,n=e.currentTile.index,r=e.tiles[n],i=r.codingStyleDefaultParameters.layersCount,s=t.Csiz,o=0;for(var u=0;u<s;u++)o=Math.max(o,r.components[u].codingStyleParameters.decompositionLevelsCount);var f=0,l=0,c=0,h=0;this.nextPacket=function(){for(;f<=o;f++){for(;l<i;l++){for(;c<s;c++){var t=r.components[c];if(f>t.codingStyleParameters.decompositionLevelsCount)continue;var n=t.resolutions[f],u=n.precinctParameters.numprecincts;for(;h<u;){var p=a(n,h,l);return h++,p}h=0}c=0}l=0}}}function c(e){var t=e.SIZ,n=e.currentTile.index,r=e.tiles[n],i=r.codingStyleDefaultParameters.layersCount,s=t.Csiz,o,u,f,l,c=0;for(f=0;f<s;f++){var h=r.components[f];c=Math.max(c,h.codingStyleParameters.decompositionLevelsCount)}var p=new Int32Array(c+1);for(u=0;u<=c;++u){var d=0;for(f=0;f<s;++f){var v=r.components[f].resolutions;u<v.length&&(d=Math.max(d,v[u].precinctParameters.numprecincts))}p[u]=d}o=0,u=0,f=0,l=0,this.nextPacket=function(){for(;u<=c;u++){for(;l<p[u];l++){for(;f<s;f++){var t=r.components[f];if(u>t.codingStyleParameters.decompositionLevelsCount)continue;var n=t.resolutions[u],h=n.precinctParameters.numprecincts;if(l>=h)continue;for(;o<i;){var d=a(n,l,o);return o++,d}o=0}f=0}l=0}}}function h(e){var t=e.SIZ,n=e.currentTile.index,r=e.tiles[n],i=r.codingStyleDefaultParameters.layersCount,s=t.Csiz,o=v(r),u=o,f=0,l=0,c=0,h=0,p=0;this.nextPacket=function(){for(;p<u.maxNumHigh;p++){for(;h<u.maxNumWide;h++){for(;c<s;c++){var t=r.components[c],n=t.codingStyleParameters.decompositionLevelsCount;for(;l<=n;l++){var v=t.resolutions[l],m=o.components[c].resolutions[l],g=d(h,p,m,u,v);if(g===null)continue;for(;f<i;){var y=a(v,g,f);return f++,y}f=0}l=0}c=0}h=0}}}function p(e){var t=e.SIZ,n=e.currentTile.index,r=e.tiles[n],i=r.codingStyleDefaultParameters.layersCount,s=t.Csiz,o=v(r),u=0,f=0,l=0,c=0,h=0;this.nextPacket=function(){for(;l<s;++l){var t=r.components[l],n=o.components[l],p=t.codingStyleParameters.decompositionLevelsCount;for(;h<n.maxNumHigh;h++){for(;c<n.maxNumWide;c++){for(;f<=p;f++){var v=t.resolutions[f],m=n.resolutions[f],g=d(c,h,m,n,v);if(g===null)continue;for(;u<i;){var y=a(v,g,u);return u++,y}u=0}f=0}c=0}h=0}}}function d(e,t,n,r,i){var s=e*r.minWidth,o=t*r.minHeight;if(s%n.width!==0||o%n.height!==0)return null;var u=o/n.width*i.precinctParameters.numprecinctswide;return s/n.height+u}function v(e){var t=e.components.length,n=Number.MAX_VALUE,r=Number.MAX_VALUE,i=0,s=0,o=new Array(t);for(var u=0;u<t;u++){var a=e.components[u],f=a.codingStyleParameters.decompositionLevelsCount,l=new Array(f+1),c=Number.MAX_VALUE,h=Number.MAX_VALUE,p=0,d=0,v=1;for(var m=f;m>=0;--m){var g=a.resolutions[m],y=v*g.precinctParameters.precinctWidth,b=v*g.precinctParameters.precinctHeight;c=Math.min(c,y),h=Math.min(h,b),p=Math.max(p,g.precinctParameters.numprecinctswide),d=Math.max(d,g.precinctParameters.numprecinctshigh),l[m]={width:y,height:b},v<<=1}n=Math.min(n,c),r=Math.min(r,h),i=Math.max(i,p),s=Math.max(s,d),o[u]={resolutions:l,minWidth:c,minHeight:h,maxNumWide:p,maxNumHigh:d}}return{components:o,minWidth:n,minHeight:r,maxNumWide:i,maxNumHigh:s}}function m(e){var t=e.SIZ,n=e.currentTile.index,r=e.tiles[n],i=t.Csiz;for(var a=0;a<i;a++){var d=r.components[a],v=d.codingStyleParameters.decompositionLevelsCount,m=[],g=[];for(var y=0;y<=v;y++){var b=s(e,d,y),w={},E=1<<v-y;w.trx0=Math.ceil(d.tcx0/E),w.try0=Math.ceil(d.tcy0/E),w.trx1=Math.ceil(d.tcx1/E),w.try1=Math.ceil(d.tcy1/E),w.resLevel=y,o(e,w,b),m.push(w);var S;if(y===0)S={},S.type="LL",S.tbx0=Math.ceil(d.tcx0/E),S.tby0=Math.ceil(d.tcy0/E),S.tbx1=Math.ceil(d.tcx1/E),S.tby1=Math.ceil(d.tcy1/E),S.resolution=w,u(e,S,b),g.push(S),w.subbands=[S];else{var x=1<<v-y+1,T=[];S={},S.type="HL",S.tbx0=Math.ceil(d.tcx0/x-.5),S.tby0=Math.ceil(d.tcy0/x),S.tbx1=Math.ceil(d.tcx1/x-.5),S.tby1=Math.ceil(d.tcy1/x),S.resolution=w,u(e,S,b),g.push(S),T.push(S),S={},S.type="LH",S.tbx0=Math.ceil(d.tcx0/x),S.tby0=Math.ceil(d.tcy0/x-.5),S.tbx1=Math.ceil(d.tcx1/x),S.tby1=Math.ceil(d.tcy1/x-.5),S.resolution=w,u(e,S,b),g.push(S),T.push(S),S={},S.type="HH",S.tbx0=Math.ceil(d.tcx0/x-.5),S.tby0=Math.ceil(d.tcy0/x-.5),S.tbx1=Math.ceil(d.tcx1/x-.5),S.tby1=Math.ceil(d.tcy1/x-.5),S.resolution=w,u(e,S,b),g.push(S),T.push(S),w.subbands=T}}d.resolutions=m,d.subbands=g}var N=r.codingStyleDefaultParameters.progressionOrder;switch(N){case 0:r.packetsIterator=new f(e);break;case 1:r.packetsIterator=new l(e);break;case 2:r.packetsIterator=new c(e);break;case 3:r.packetsIterator=new h(e);break;case 4:r.packetsIterator=new p(e);break;default:throw new Error("JPX Error: Unsupported progression order "+N)}}function g(e,t,n,r){function a(e){while(o<e){var r=t[n+i];i++,u?(s=s<<7|r,o+=7,u=!1):(s=s<<8|r,o+=8),r===255&&(u=!0)}return o-=e,s>>>o&(1<<e)-1}function f(e){return t[n+i-1]===255&&t[n+i]===e?(l(1),!0):t[n+i]===255&&t[n+i+1]===e?(l(2),!0):!1}function l(e){i+=e}function c(){o=0,u&&(i++,u=!1)}function h(){if(a(1)===0)return 1;if(a(1)===0)return 2;var e=a(2);return e<3?e+3:(e=a(5),e<31?e+6:(e=a(7),e+37))}var i=0,s,o=0,u=!1,p=e.currentTile.index,d=e.tiles[p],v=e.COD.sopMarkerUsed,m=e.COD.ephMarkerUsed,g=d.packetsIterator;while(i<r){c(),v&&f(145)&&l(4);var y=g.nextPacket();if(y===undefined)return;if(!a(1))continue;var b=y.layerNumber,w=[],E;for(var T=0,N=y.codeblocks.length;T<N;T++){E=y.codeblocks[T];var C=E.precinct,k=E.cbx-C.cbxMin,L=E.cby-C.cbyMin,A=!1,O=!1,M;if(E.included!==undefined)A=!!a(1);else{C=E.precinct;var _,D;if(C.inclusionTree!==undefined)_=C.inclusionTree;else{var P=C.cbxMax-C.cbxMin+1,H=C.cbyMax-C.cbyMin+1;_=new x(P,H,b),D=new S(P,H),C.inclusionTree=_,C.zeroBitPlanesTree=D;for(var B=0;B<b;B++)if(a(1)!==0)throw new Error("JPX Error: Invalid tag tree")}if(_.reset(k,L,b))for(;;){if(!a(1)){_.incrementValue(b);break}M=!_.nextLevel();if(M){E.included=!0,A=O=!0;break}}}if(!A)continue;if(O){D=C.zeroBitPlanesTree,D.reset(k,L);for(;;)if(a(1)){M=!D.nextLevel();if(M)break}else D.incrementValue();E.zeroBitPlanes=D.value}var j=h();while(a(1))E.Lblock++;var F=log2(j),I=(j<1<<F?F-1:F)+E.Lblock,q=a(I);w.push({codeblock:E,codingpasses:j,dataLength:q})}c(),m&&f(146);while(w.length>0){var R=w.shift();E=R.codeblock,E.data===undefined&&(E.data=[]),E.data.push({data:t,start:n+i,end:n+i+R.dataLength,codingpasses:R.codingpasses}),i+=R.dataLength}}return i}function y(e,t,n,r,i,s,o,u){var a=r.tbx0,f=r.tby0,l=r.tbx1-r.tbx0,c=r.codeblocks,h=r.type.charAt(0)==="H"?1:0,p=r.type.charAt(1)==="H"?t:0;for(var d=0,v=c.length;d<v;++d){var m=c[d],g=m.tbx1_-m.tbx0_,y=m.tby1_-m.tby0_;if(g===0||y===0)continue;if(m.data===undefined)continue;var b,w;b=new T(g,y,m.subbandType,m.zeroBitPlanes,s),w=2;var E=m.data,S=0,x=0,N,C,k;for(N=0,C=E.length;N<C;N++)k=E[N],S+=k.end-k.start,x+=k.codingpasses;var L=new Int16Array(S),A=0;for(N=0,C=E.length;N<C;N++){k=E[N];var O=k.data.subarray(k.start,k.end);L.set(O,A),A+=O.length}var M=new ArithmeticDecoder(L,0,S);b.setDecoder(M);for(N=0;N<x;N++){switch(w){case 0:b.runSignificancePropogationPass();break;case 1:b.runMagnitudeRefinementPass();break;case 2:b.runCleanupPass(),u&&b.checkSegmentationSymbol()}w=(w+1)%3}var _=m.tbx0_-a+(m.tby0_-f)*l,D=b.coefficentsSign,P=b.coefficentsMagnitude,H=b.bitsDecoded,B=o?0:.5,j,F,I;A=0;var q=r.type!=="LL";for(N=0;N<y;N++){var R=_/l|0,U=2*R*(t-l)+h+p;for(j=0;j<g;j++){F=P[A];if(F!==0){F=(F+B)*i,D[A]!==0&&(F=-F),I=H[A];var z=q?U+(_<<1):_;o&&I>=s?e[z]=F:e[z]=F*(1<<s-I)}_++,A++}_+=l-g}}}function b(e,n,r){var i=n.components[r],s=i.codingStyleParameters,o=i.quantizationParameters,u=s.decompositionLevelsCount,a=o.SPqcds,f=o.scalarExpounded,l=o.guardBits,c=s.segmentationSymbolUsed,h=e.components[r].precision,p=s.reversibleTransformation,d=p?new k:new C,v=[],m=0;for(var g=0;g<=u;g++){var b=i.resolutions[g],w=b.trx1-b.trx0,E=b.try1-b.try0,S=new Float32Array(w*E);for(var x=0,T=b.subbands.length;x<T;x++){var N,L;f?(N=a[m].mu,L=a[m].epsilon,m++):(N=a[0].mu,L=a[0].epsilon+(g>0?1-g:0));var A=b.subbands[x],O=t[A.type],M=p?1:Math.pow(2,h+O-L)*(1+N/2048),_=l+L-1;y(S,w,E,A,M,_,p,c)}v.push({width:w,height:E,items:S})}var D=d.calculate(v,i.tcx0,i.tcy0);return{left:i.tcx0,top:i.tcy0,width:D.width,height:D.height,items:D.items}}function w(e){var t=e.SIZ,n=e.components,r=t.Csiz,i=[];for(var s=0,o=e.tiles.length;s<o;s++){var u=e.tiles[s],a=[],f;for(f=0;f<r;f++)a[f]=b(e,u,f);var l=a[0],c=new Int16Array(l.items.length*r),h={left:l.left,top:l.top,width:l.width,height:l.height,items:c},p,d,v,m,g,y=0,w,E,S,x,T,N,C,k,L,A;if(u.codingStyleDefaultParameters.multipleComponentTransform){var O=r===4,M=a[0].items,_=a[1].items,D=a[2].items,P=O?a[3].items:null;p=n[0].precision-8,d=(128<<p)+.5,v=255*(1<<p),g=v*.5,m=-g;var H=u.components[0],B=r-3;E=M.length;if(!H.codingStyleParameters.reversibleTransformation)for(w=0;w<E;w++,y+=B)S=M[w]+d,x=_[w],T=D[w],N=S+1.402*T,C=S-.34413*x-.71414*T,k=S+1.772*x,c[y++]=N<=0?0:N>=v?255:N>>p,c[y++]=C<=0?0:C>=v?255:C>>p,c[y++]=k<=0?0:k>=v?255:k>>p;else for(w=0;w<E;w++,y+=B)S=M[w]+d,x=_[w],T=D[w],C=S-(T+x>>2),N=C+T,k=C+x,c[y++]=N<=0?0:N>=v?255:N>>p,c[y++]=C<=0?0:C>=v?255:C>>p,c[y++]=k<=0?0:k>=v?255:k>>p;if(O)for(w=0,y=3;w<E;w++,y+=4)L=P[w],c[y]=L<=m?0:L>=g?255:L+d>>p}else for(f=0;f<r;f++)if(n[f].precision===8){var j=a[f].items;p=n[f].precision-8,d=(128<<p)+.5,v=127.5*(1<<p),m=-v;for(y=f,w=0,E=j.length;w<E;w++)A=j[w],c[y]=A<=m?0:A>=v?255:A+d>>p,y+=r}else{var F=n[f].isSigned,j=a[f].items;F?(p=0,d=0):(p=n[f].precision-8,d=(128<<p)+.5);for(y=f,w=0,E=j.length;w<E;w++)A=j[w],c[y]=A+d,y+=r}i.push(h)}return i}function E(e,t){var n=e.SIZ,r=n.Csiz,i=e.tiles[t];for(var s=0;s<r;s++){var o=i.components[s],u=e.currentTile.QCC[s]!==undefined?e.currentTile.QCC[s]:e.currentTile.QCD;o.quantizationParameters=u;var a=e.currentTile.COC[s]!==undefined?e.currentTile.COC[s]:e.currentTile.COD;o.codingStyleParameters=a}i.codingStyleDefaultParameters=e.currentTile.COD}var t={LL:0,LH:1,HL:1,HH:2};n.prototype={parse:function(t){var n=readUint16(t,0);if(n===65359){this.parseCodestream(t,0,t.length);return}var r=0,i=t.length;while(r<i){var s=8,o=readUint32(t,r),u=readUint32(t,r+4);r+=s,o===1&&(o=readUint32(t,r)*4294967296+readUint32(t,r+4),r+=8,s+=8),o===0&&(o=i-r+s);if(o<s)throw new Error("JPX Error: Invalid box field size");var a=o-s,f=!0;switch(u){case 1785737832:f=!1;break;case 1668246642:var l=t[r],c=t[r+1],h=t[r+2];if(l===1){var p=readUint32(t,r+3);switch(p){case 16:case 17:case 18:break;default:warn("Unknown colorspace "+p)}}else l===2&&info("ICC profile not supported");break;case 1785737827:this.parseCodestream(t,r,r+a);break;case 1783636e3:218793738!==readUint32(t,r)&&warn("Invalid JP2 signature");break;case 1783634458:case 1718909296:case 1920099697:case 1919251232:case 1768449138:break;default:var d=String.fromCharCode(u>>24&255,u>>16&255,u>>8&255,u&255);warn("Unsupported header type "+u+" ("+d+")")}f&&(r+=a)}},parseImageProperties:function(t){var n=t.getByte();while(n>=0){var r=n;n=t.getByte();var i=r<<8|n;if(i===65361){t.skip(4);var s=t.getInt32()>>>0,o=t.getInt32()>>>0,u=t.getInt32()>>>0,a=t.getInt32()>>>0;t.skip(16);var f=t.getUint16();this.width=s-u,this.height=o-a,this.componentsCount=f,this.bitsPerComponent=8;return}}throw new Error("JPX Error: No size marker found in JPX stream")},parseCodestream:function(t,n,s){var o={};try{var u=!1,a=n;while(a+1<s){var f=readUint16(t,a);a+=2;var l=0,c,h,p,d,v,y;switch(f){case 65359:o.mainHeader=!0;break;case 65497:break;case 65361:l=readUint16(t,a);var b={};b.Xsiz=readUint32(t,a+4),b.Ysiz=readUint32(t,a+8),b.XOsiz=readUint32(t,a+12),b.YOsiz=readUint32(t,a+16),b.XTsiz=readUint32(t,a+20),b.YTsiz=readUint32(t,a+24),b.XTOsiz=readUint32(t,a+28),b.YTOsiz=readUint32(t,a+32);var S=readUint16(t,a+36);b.Csiz=S;var x=[];c=a+38;for(var T=0;T<S;T++){var N={precision:(t[c]&127)+1,isSigned:!!(t[c]&128),XRsiz:t[c+1],YRsiz:t[c+1]};r(N,b),x.push(N)}o.SIZ=b,o.components=x,i(o,x),o.QCC=[],o.COC=[];break;case 65372:l=readUint16(t,a);var C={};c=a+2,h=t[c++];switch(h&31){case 0:d=8,v=!0;break;case 1:d=16,v=!1;break;case 2:d=16,v=!0;break;default:throw new Error("JPX Error: Invalid SQcd value "+h)}C.noQuantization=d===8,C.scalarExpounded=v,C.guardBits=h>>5,p=[];while(c<l+a){var k={};d===8?(k.epsilon=t[c++]>>3,k.mu=0):(k.epsilon=t[c]>>3,k.mu=(t[c]&7)<<8|t[c+1],c+=2),p.push(k)}C.SPqcds=p,o.mainHeader?o.QCD=C:(o.currentTile.QCD=C,o.currentTile.QCC=[]);break;case 65373:l=readUint16(t,a);var L={};c=a+2;var A;o.SIZ.Csiz<257?A=t[c++]:(A=readUint16(t,c),c+=2),h=t[c++];switch(h&31){case 0:d=8,v=!0;break;case 1:d=16,v=!1;break;case 2:d=16,v=!0;break;default:throw new Error("JPX Error: Invalid SQcd value "+h)}L.noQuantization=d===8,L.scalarExpounded=v,L.guardBits=h>>5,p=[];while(c<l+a)k={},d===8?(k.epsilon=t[c++]>>3,k.mu=0):(k.epsilon=t[c]>>3,k.mu=(t[c]&7)<<8|t[c+1],c+=2),p.push(k);L.SPqcds=p,o.mainHeader?o.QCC[A]=L:o.currentTile.QCC[A]=L;break;case 65362:l=readUint16(t,a);var O={};c=a+2;var M=t[c++];O.entropyCoderWithCustomPrecincts=!!(M&1),O.sopMarkerUsed=!!(M&2),O.ephMarkerUsed=!!(M&4),O.progressionOrder=t[c++],O.layersCount=readUint16(t,c),c+=2,O.multipleComponentTransform=t[c++],O.decompositionLevelsCount=t[c++],O.xcb=(t[c++]&15)+2,O.ycb=(t[c++]&15)+2;var _=t[c++];O.selectiveArithmeticCodingBypass=!!(_&1),O.resetContextProbabilities=!!(_&2),O.terminationOnEachCodingPass=!!(_&4),O.verticalyStripe=!!(_&8),O.predictableTermination=!!(_&16),O.segmentationSymbolUsed=!!(_&32),O.reversibleTransformation=t[c++];if(O.entropyCoderWithCustomPrecincts){var D=[];while(c<l+a){var P=t[c++];D.push({PPx:P&15,PPy:P>>4})}O.precinctsSizes=D}var H=[];O.selectiveArithmeticCodingBypass&&H.push("selectiveArithmeticCodingBypass"),O.resetContextProbabilities&&H.push("resetContextProbabilities"),O.terminationOnEachCodingPass&&H.push("terminationOnEachCodingPass"),O.verticalyStripe&&H.push("verticalyStripe"),O.predictableTermination&&H.push("predictableTermination");if(H.length>0)throw u=!0,new Error("JPX Error: Unsupported COD options ("+H.join(", ")+")");o.mainHeader?o.COD=O:(o.currentTile.COD=O,o.currentTile.COC=[]);break;case 65424:l=readUint16(t,a),y={},y.index=readUint16(t,a+2),y.length=readUint32(t,a+4),y.dataEnd=y.length+a-2,y.partIndex=t[a+8],y.partsCount=t[a+9],o.mainHeader=!1,y.partIndex===0&&(y.COD=o.COD,y.COC=o.COC.slice(0),y.QCD=o.QCD,y.QCC=o.QCC.slice(0)),o.currentTile=y;break;case 65427:y=o.currentTile,y.partIndex===0&&(E(o,y.index),m(o)),l=y.dataEnd-a,g(o,t,a,l);break;case 65365:case 65367:case 65368:case 65380:l=readUint16(t,a);break;case 65363:throw new Error("JPX Error: Codestream code 0xFF53 (COC) is not implemented");default:throw new Error("JPX Error: Unknown codestream code: "+f.toString(16))}a+=l}}catch(B){if(u||this.failOnCorruptedImage)throw B;warn("Trying to recover from "+B.message)}this.tiles=w(o),this.width=o.SIZ.Xsiz-o.SIZ.XOsiz,this.height=o.SIZ.Ysiz-o.SIZ.YOsiz,this.componentsCount=o.SIZ.Csiz}};var S=function(){function t(e,t){var n=log2(Math.max(e,t))+1;this.levels=[];for(var r=0;r<n;r++){var i={width:e,height:t,items:[]};this.levels.push(i),e=Math.ceil(e/2),t=Math.ceil(t/2)}}return t.prototype={reset:function(t,n){var r=0,i=0,s;while(r<this.levels.length){s=this.levels[r];var o=t+n*s.width;if(s.items[o]!==undefined){i=s.items[o];break}s.index=o,t>>=1,n>>=1,r++}r--,s=this.levels[r],s.items[s.index]=i,this.currentLevel=r,delete this.value},incrementValue:function(){var t=this.levels[this.currentLevel];t.items[t.index]++},nextLevel:function(){var t=this.currentLevel,n=this.levels[t],r=n.items[n.index];return t--,t<0?(this.value=r,!1):(this.currentLevel=t,n=this.levels[t],n.items[n.index]=r,!0)}},t}(),x=function(){function t(e,t,n){var r=log2(Math.max(e,t))+1;this.levels=[];for(var i=0;i<r;i++){var s=new Int16Array(e*t);for(var o=0,u=s.length;o<u;o++)s[o]=n;var a={width:e,height:t,items:s};this.levels.push(a),e=Math.ceil(e/2),t=Math.ceil(t/2)}}return t.prototype={reset:function(t,n,r){var i=0;while(i<this.levels.length){var s=this.levels[i],o=t+n*s.width;s.index=o;var u=s.items[o];if(u===255)break;if(u>r)return this.currentLevel=i,this.propagateValues(),!1;t>>=1,n>>=1,i++}return this.currentLevel=i-1,!0},incrementValue:function(t){var n=this.levels[this.currentLevel];n.items[n.index]=t+1,this.propagateValues()},propagateValues:function(){var t=this.currentLevel,n=this.levels[t],r=n.items[n.index];while(--t>=0)n=this.levels[t],n.items[n.index]=r},nextLevel:function(){var t=this.currentLevel,n=this.levels[t],r=n.items[n.index];return n.items[n.index]=255,t--,t<0?!1:(this.currentLevel=t,n=this.levels[t],n.items[n.index]=r,!0)}},t}(),T=function(){function o(e,t,n,o,u){this.width=e,this.height=t,this.contextLabelTable=n==="HH"?s:n==="HL"?i:r;var a=e*t;this.neighborsSignificance=new Uint8Array(a),this.coefficentsSign=new Uint8Array(a),this.coefficentsMagnitude=u>14?new Uint32Array(a):u>6?new Uint16Array(a):new Uint8Array(a),this.processingFlags=new Uint8Array(a);var f=new Uint8Array(a);if(o!==0)for(var l=0;l<a;l++)f[l]=o;this.bitsDecoded=f,this.reset()}var t=17,n=18,r=new Uint8Array([0,5,8,0,3,7,8,0,4,7,8,0,0,0,0,0,1,6,8,0,3,7,8,0,4,7,8,0,0,0,0,0,2,6,8,0,3,7,8,0,4,7,8,0,0,0,0,0,2,6,8,0,3,7,8,0,4,7,8,0,0,0,0,0,2,6,8,0,3,7,8,0,4,7,8]),i=new Uint8Array([0,3,4,0,5,7,7,0,8,8,8,0,0,0,0,0,1,3,4,0,6,7,7,0,8,8,8,0,0,0,0,0,2,3,4,0,6,7,7,0,8,8,8,0,0,0,0,0,2,3,4,0,6,7,7,0,8,8,8,0,0,0,0,0,2,3,4,0,6,7,7,0,8,8,8]),s=new Uint8Array([0,1,2,0,1,2,2,0,2,2,2,0,0,0,0,0,3,4,5,0,4,5,5,0,5,5,5,0,0,0,0,0,6,7,7,0,7,7,7,0,7,7,7,0,0,0,0,0,8,8,8,0,8,8,8,0,8,8,8,0,0,0,0,0,8,8,8,0,8,8,8,0,8,8,8]);return o.prototype={setDecoder:function(t){this.decoder=t},reset:function(){this.contexts=new Int8Array(19),this.contexts[0]=8,this.contexts[t]=92,this.contexts[n]=6},setNeighborsSignificance:function(t,n,r){var i=this.neighborsSignificance,s=this.width,o=this.height,u=n>0,a=n+1<s,f;t>0&&(f=r-s,u&&(i[f-1]+=16),a&&(i[f+1]+=16),i[f]+=4),t+1<o&&(f=r+s,u&&(i[f-1]+=16),a&&(i[f+1]+=16),i[f]+=4),u&&(i[r-1]+=1),a&&(i[r+1]+=1),i[r]|=128},runSignificancePropogationPass:function(){var t=this.decoder,n=this.width,r=this.height,i=this.coefficentsMagnitude,s=this.coefficentsSign,o=this.neighborsSignificance,u=this.processingFlags,a=this.contexts,f=this.contextLabelTable,l=this.bitsDecoded,c=-2,h=1,p=2;for(var d=0;d<r;d+=4)for(var v=0;v<n;v++){var m=d*n+v;for(var g=0;g<4;g++,m+=n){var y=d+g;if(y>=r)break;u[m]&=c;if(i[m]||!o[m])continue;var b=f[o[m]],w=t.readBit(a,b);if(w){var E=this.decodeSignBit(y,v,m);s[m]=E,i[m]=1,this.setNeighborsSignificance(y,v,m),u[m]|=p}l[m]++,u[m]|=h}}},decodeSignBit:function(t,n,r){var i=this.width,s=this.height,o=this.coefficentsMagnitude,u=this.coefficentsSign,a,f,l,c,h,p;c=n>0&&o[r-1]!==0,n+1<i&&o[r+1]!==0?(l=u[r+1],c?(f=u[r-1],a=1-l-f):a=1-l-l):c?(f=u[r-1],a=1-f-f):a=0;var d=3*a;return c=t>0&&o[r-i]!==0,t+1<s&&o[r+i]!==0?(l=u[r+i],c?(f=u[r-i],a=1-l-f+d):a=1-l-l+d):c?(f=u[r-i],a=1-f-f+d):a=d,a>=0?(h=9+a,p=this.decoder.readBit(this.contexts,h)):(h=9-a,p=this.decoder.readBit(this.contexts,h)^1),p},runMagnitudeRefinementPass:function(){var t=this.decoder,n=this.width,r=this.height,i=this.coefficentsMagnitude,s=this.neighborsSignificance,o=this.contexts,u=this.bitsDecoded,a=this.processingFlags,f=1,l=2,c=n*r,h=n*4;for(var p=0,d;p<c;p=d){d=Math.min(c,p+h);for(var v=0;v<n;v++)for(var m=p+v;m<d;m+=n){if(!i[m]||(a[m]&f)!==0)continue;var g=16;if((a[m]&l)!==0){a[m]^=l;var y=s[m]&127;g=y===0?15:14}var b=t.readBit(o,g);i[m]=i[m]<<1|b,u[m]++,a[m]|=f}}},runCleanupPass:function(){var r=this.decoder,i=this.width,s=this.height,o=this.neighborsSignificance,u=this.coefficentsMagnitude,a=this.coefficentsSign,f=this.contexts,l=this.contextLabelTable,c=this.bitsDecoded,h=this.processingFlags,p=1,d=2,v=i,m=i*2,g=i*3,y;for(var b=0;b<s;b=y){y=Math.min(b+4,s);var w=b*i,E=b+3<s;for(var S=0;S<i;S++){var x=w+S,T=E&&h[x]===0&&h[x+v]===0&&h[x+m]===0&&h[x+g]===0&&o[x]===0&&o[x+v]===0&&o[x+m]===0&&o[x+g]===0,N=0,C=x,k=b,L;if(T){var A=r.readBit(f,n);if(!A){c[x]++,c[x+v]++,c[x+m]++,c[x+g]++;continue}N=r.readBit(f,t)<<1|r.readBit(f,t),N!==0&&(k=b+N,C+=N*i),L=this.decodeSignBit(k,S,C),a[C]=L,u[C]=1,this.setNeighborsSignificance(k,S,C),h[C]|=d,C=x;for(var O=b;O<=k;O++,C+=i)c[C]++;N++}for(k=b+N;k<y;k++,C+=i){if(u[C]||(h[C]&p)!==0)continue;var M=l[o[C]],_=r.readBit(f,M);_===1&&(L=this.decodeSignBit(k,S,C),a[C]=L,u[C]=1,this.setNeighborsSignificance(k,S,C),h[C]|=d),c[C]++}}}},checkSegmentationSymbol:function(){var n=this.decoder,r=this.contexts,i=n.readBit(r,t)<<3|n.readBit(r,t)<<2|n.readBit(r,t)<<1|n.readBit(r,t);if(i!==10)throw new Error("JPX Error: Invalid segmentation symbol")}},o}(),N=function(){function t(){}return t.prototype.calculate=function(t,n,r){var i=t[0];for(var s=1,o=t.length;s<o;s++)i=this.iterate(i,t[s],n,r);return i},t.prototype.extend=function(t,n,r){var i=n-1,s=n+1,o=n+r-2,u=n+r;t[i--]=t[s++],t[u++]=t[o--],t[i--]=t[s++],t[u++]=t[o--],t[i--]=t[s++],t[u++]=t[o--],t[i]=t[s],t[u]=t[o]},t.prototype.iterate=function(t,n,r,i){var s=t.width,o=t.height,u=t.items,a=n.width,f=n.height,l=n.items,c,h,p,d,v,m;for(p=0,c=0;c<o;c++){d=c*2*a;for(h=0;h<s;h++,p++,d+=2)l[d]=u[p]}u=t.items=null;var g=4,y=new Float32Array(a+2*g);if(a===1){if((r&1)!==0)for(m=0,p=0;m<f;m++,p+=a)l[p]*=.5}else for(m=0,p=0;m<f;m++,p+=a)y.set(l.subarray(p,p+a),g),this.extend(y,g,a),this.filter(y,g,a),l.set(y.subarray(g,g+a),p);var b=16,w=[];for(c=0;c<b;c++)w.push(new Float32Array(f+2*g));var E,S=0;t=g+f;if(f===1){if((i&1)!==0)for(v=0;v<a;v++)l[v]*=.5}else for(v=0;v<a;v++){if(S===0){b=Math.min(a-v,b);for(p=v,d=g;d<t;p+=a,d++)for(E=0;E<b;E++)w[E][d]=l[p+E];S=b}S--;var x=w[S];this.extend(x,g,f),this.filter(x,g,f);if(S===0){p=v-b+1;for(d=g;d<t;p+=a,d++)for(E=0;E<b;E++)l[p+E]=w[E][d]}}return{width:a,height:f,items:l}},t}(),C=function(){function t(){N.call(this)}return t.prototype=Object.create(N.prototype),t.prototype.filter=function(t,n,r){var i=r>>1;n|=0;var s,o,u,a,f=-1.586134342059924,l=-0.052980118572961,c=.882911075530934,h=.443506852043971,p=1.230174104914001,d=1/p;s=n-3;for(o=i+4;o--;s+=2)t[s]*=d;s=n-2,u=h*t[s-1];for(o=i+3;o--;s+=2){a=h*t[s+1],t[s]=p*t[s]-u-a;if(!(o--))break;s+=2,u=h*t[s+1],t[s]=p*t[s]-u-a}s=n-1,u=c*t[s-1];for(o=i+2;o--;s+=2){a=c*t[s+1],t[s]-=u+a;if(!(o--))break;s+=2,u=c*t[s+1],t[s]-=u+a}s=n,u=l*t[s-1];for(o=i+1;o--;s+=2){a=l*t[s+1],t[s]-=u+a;if(!(o--))break;s+=2,u=l*t[s+1],t[s]-=u+a}if(i!==0){s=n+1,u=f*t[s-1];for(o=i;o--;s+=2){a=f*t[s+1],t[s]-=u+a;if(!(o--))break;s+=2,u=f*t[s+1],t[s]-=u+a}}},t}(),k=function(){function t(){N.call(this)}return t.prototype=Object.create(N.prototype),t.prototype.filter=function(t,n,r){var i=r>>1;n|=0;var s,o;for(s=n,o=i+1;o--;s+=2)t[s]-=t[s-1]+t[s+1]+2>>2;for(s=n+1,o=i;o--;s+=2)t[s]+=t[s-1]+t[s+1]>>1},t}();return n}(),ArithmeticDecoder=function(){function n(e,t,n){this.data=e,this.bp=t,this.dataEnd=n,this.chigh=e[t],this.clow=0,this.byteIn(),this.chigh=this.chigh<<7&65535|this.clow>>9&127,this.clow=this.clow<<7&65535,this.ct-=7,this.a=32768}var t=[{qe:22017,nmps:1,nlps:1,switchFlag:1},{qe:13313,nmps:2,nlps:6,switchFlag:0},{qe:6145,nmps:3,nlps:9,switchFlag:0},{qe:2753,nmps:4,nlps:12,switchFlag:0},{qe:1313,nmps:5,nlps:29,switchFlag:0},{qe:545,nmps:38,nlps:33,switchFlag:0},{qe:22017,nmps:7,nlps:6,switchFlag:1},{qe:21505,nmps:8,nlps:14,switchFlag:0},{qe:18433,nmps:9,nlps:14,switchFlag:0},{qe:14337,nmps:10,nlps:14,switchFlag:0},{qe:12289,nmps:11,nlps:17,switchFlag:0},{qe:9217,nmps:12,nlps:18,switchFlag:0},{qe:7169,nmps:13,nlps:20,switchFlag:0},{qe:5633,nmps:29,nlps:21,switchFlag:0},{qe:22017,nmps:15,nlps:14,switchFlag:1},{qe:21505,nmps:16,nlps:14,switchFlag:0},{qe:20737,nmps:17,nlps:15,switchFlag:0},{qe:18433,nmps:18,nlps:16,switchFlag:0},{qe:14337,nmps:19,nlps:17,switchFlag:0},{qe:13313,nmps:20,nlps:18,switchFlag:0},{qe:12289,nmps:21,nlps:19,switchFlag:0},{qe:10241,nmps:22,nlps:19,switchFlag:0},{qe:9217,nmps:23,nlps:20,switchFlag:0},{qe:8705,nmps:24,nlps:21,switchFlag:0},{qe:7169,nmps:25,nlps:22,switchFlag:0},{qe:6145,nmps:26,nlps:23,switchFlag:0},{qe:5633,nmps:27,nlps:24,switchFlag:0},{qe:5121,nmps:28,nlps:25,switchFlag:0},{qe:4609,nmps:29,nlps:26,switchFlag:0},{qe:4353,nmps:30,nlps:27,switchFlag:0},{qe:2753,nmps:31,nlps:28,switchFlag:0},{qe:2497,nmps:32,nlps:29,switchFlag:0},{qe:2209,nmps:33,nlps:30,switchFlag:0},{qe:1313,nmps:34,nlps:31,switchFlag:0},{qe:1089,nmps:35,nlps:32,switchFlag:0},{qe:673,nmps:36,nlps:33,switchFlag:0},{qe:545,nmps:37,nlps:34,switchFlag:0},{qe:321,nmps:38,nlps:35,switchFlag:0},{qe:273,nmps:39,nlps:36,switchFlag:0},{qe:133,nmps:40,nlps:37,switchFlag:0},{qe:73,nmps:41,nlps:38,switchFlag:0},{qe:37,nmps:42,nlps:39,switchFlag:0},{qe:21,nmps:43,nlps:40,switchFlag:0},{qe:9,nmps:44,nlps:41,switchFlag:0},{qe:5,nmps:45,nlps:42,switchFlag:0},{qe:1,nmps:45,nlps:43,switchFlag:0},{qe:22017,nmps:46,nlps:46,switchFlag:0}];return n.prototype={byteIn:function(){var t=this.data,n=this.bp;if(t[n]===255){var r=t[n+1];r>143?(this.clow+=65280,this.ct=8):(n++,this.clow+=t[n]<<9,this.ct=7,this.bp=n)}else n++,this.clow+=n<this.dataEnd?t[n]<<8:65280,this.ct=8,this.bp=n;this.clow>65535&&(this.chigh+=this.clow>>16,this.clow&=65535)},readBit:function(n,r){var i=n[r]>>1,s=n[r]&1,o=t[i],u=o.qe,a,f=this.a-u;if(this.chigh<u)f<u?(f=u,a=s,i=o.nmps):(f=u,a=1^s,o.switchFlag===1&&(s=a),i=o.nlps);else{this.chigh-=u;if((f&32768)!==0)return this.a=f,s;f<u?(a=1^s,o.switchFlag===1&&(s=a),i=o.nlps):(a=s,i=o.nmps)}do this.ct===0&&this.byteIn(),f<<=1,this.chigh=this.chigh<<1&65535|this.clow>>15&1,this.clow=this.clow<<1&65535,this.ct--;while((f&32768)===0);return this.a=f,n[r]=i<<1|s,a}},n}(),globalScope=typeof window=="undefined"?this:window,isWorker=typeof window=="undefined",FONT_IDENTITY_MATRIX=[.001,0,0,.001,0,0],TextRenderingMode={FILL:0,STROKE:1,FILL_STROKE:2,INVISIBLE:3,FILL_ADD_TO_PATH:4,STROKE_ADD_TO_PATH:5,FILL_STROKE_ADD_TO_PATH:6,ADD_TO_PATH:7,FILL_STROKE_MASK:3,ADD_TO_PATH_FLAG:4},ImageKind={GRAYSCALE_1BPP:1,RGB_24BPP:2,RGBA_32BPP:3},AnnotationType={WIDGET:1,TEXT:2,LINK:3},StreamType={UNKNOWN:0,FLATE:1,LZW:2,DCT:3,JPX:4,JBIG:5,A85:6,AHX:7,CCF:8,RL:9},FontType={UNKNOWN:0,TYPE1:1,TYPE1C:2,CIDFONTTYPE0:3,CIDFONTTYPE0C:4,TRUETYPE:5,CIDFONTTYPE2:6,TYPE3:7,OPENTYPE:8,TYPE0:9,MMTYPE1:10};globalScope.PDFJS||(globalScope.PDFJS={}),globalScope.PDFJS.pdfBug=!1,PDFJS.VERBOSITY_LEVELS={errors:0,warnings:1,infos:5};var OPS=PDFJS.OPS={dependency:1,setLineWidth:2,setLineCap:3,setLineJoin:4,setMiterLimit:5,setDash:6,setRenderingIntent:7,setFlatness:8,setGState:9,save:10,restore:11,transform:12,moveTo:13,lineTo:14,curveTo:15,curveTo2:16,curveTo3:17,closePath:18,rectangle:19,stroke:20,closeStroke:21,fill:22,eoFill:23,fillStroke:24,eoFillStroke:25,closeFillStroke:26,closeEOFillStroke:27,endPath:28,clip:29,eoClip:30,beginText:31,endText:32,setCharSpacing:33,setWordSpacing:34,setHScale:35,setLeading:36,setFont:37,setTextRenderingMode:38,setTextRise:39,moveText:40,setLeadingMoveText:41,setTextMatrix:42,nextLine:43,showText:44,showSpacedText:45,nextLineShowText:46,nextLineSetSpacingShowText:47,setCharWidth:48,setCharWidthAndBounds:49,setStrokeColorSpace:50,setFillColorSpace:51,setStrokeColor:52,setStrokeColorN:53,setFillColor:54,setFillColorN:55,setStrokeGray:56,setFillGray:57,setStrokeRGBColor:58,setFillRGBColor:59,setStrokeCMYKColor:60,setFillCMYKColor:61,shadingFill:62,beginInlineImage:63,beginImageData:64,endInlineImage:65,paintXObject:66,markPoint:67,markPointProps:68,beginMarkedContent:69,beginMarkedContentProps:70,endMarkedContent:71,beginCompat:72,endCompat:73,paintFormXObjectBegin:74,paintFormXObjectEnd:75,beginGroup:76,endGroup:77,beginAnnotations:78,endAnnotations:79,beginAnnotation:80,endAnnotation:81,paintJpegXObject:82,paintImageMaskXObject:83,paintImageMaskXObjectGroup:84,paintImageXObject:85,paintInlineImageXObject:86,paintInlineImageXObjectGroup:87,paintImageXObjectRepeat:88,paintImageMaskXObjectRepeat:89,paintSolidColorImageMask:90,constructPath:91},UNSUPPORTED_FEATURES=PDFJS.UNSUPPORTED_FEATURES={unknown:"unknown",forms:"forms",javaScript:"javaScript",smask:"smask",shadingPattern:"shadingPattern",font:"font"},UnsupportedManager=PDFJS.UnsupportedManager=function(){var t=[];return{listen:function(e){t.push(e)},notify:function(e){warn('Unsupported feature "'+e+'"');for(var n=0,r=t.length;n<r;n++)t[n](e)}}}();PDFJS.isValidUrl=isValidUrl,PDFJS.shadow=shadow;var PasswordResponses=PDFJS.PasswordResponses={NEED_PASSWORD:1,INCORRECT_PASSWORD:2},PasswordException=function(){function t(e,t){this.name="PasswordException",this.message=e,this.code=t}return t.prototype=new Error,t.constructor=t,t}();PDFJS.PasswordException=PasswordException;var UnknownErrorException=function(){function t(e,t){this.name="UnknownErrorException",this.message=e,this.details=t}return t.prototype=new Error,t.constructor=t,t}();PDFJS.UnknownErrorException=UnknownErrorException;var InvalidPDFException=function(){function t(e){this.name="InvalidPDFException",this.message=e}return t.prototype=new Error,t.constructor=t,t}();PDFJS.InvalidPDFException=InvalidPDFException;var MissingPDFException=function(){function t(e){this.name="MissingPDFException",this.message=e}return t.prototype=new Error,t.constructor=t,t}();PDFJS.MissingPDFException=MissingPDFException;var UnexpectedResponseException=function(){function t(e,t){this.name="UnexpectedResponseException",this.message=e,this.status=t}return t.prototype=new Error,t.constructor=t,t}();PDFJS.UnexpectedResponseException=UnexpectedResponseException;var NotImplementedException=function(){function t(e){this.message=e}return t.prototype=new Error,t.prototype.name="NotImplementedException",t.constructor=t,t}(),MissingDataException=function(){function t(e,t){this.begin=e,this.end=t,this.message="Missing data ["+e+", "+t+")"}return t.prototype=new Error,t.prototype.name="MissingDataException",t.constructor=t,t}(),XRefParseException=function(){function t(e){this.message=e}return t.prototype=new Error,t.prototype.name="XRefParseException",t.constructor=t,t}();Object.defineProperty(PDFJS,"isLittleEndian",{configurable:!0,get:function(){return shadow(PDFJS,"isLittleEndian",isLittleEndian())}}),Object.defineProperty(PDFJS,"hasCanvasTypedArrays",{configurable:!0,get:function(){return shadow(PDFJS,"hasCanvasTypedArrays",hasCanvasTypedArrays())}});var Uint32ArrayView=function(){function t(e,t){this.buffer=e,this.byteLength=e.length,this.length=t===undefined?this.byteLength>>2:t,i(this.length)}function r(e){return{get:function(){var t=this.buffer,n=e<<2;return(t[n]|t[n+1]<<8|t[n+2]<<16|t[n+3]<<24)>>>0},set:function(t){var n=this.buffer,r=e<<2;n[r]=t&255,n[r+1]=t>>8&255,n[r+2]=t>>16&255,n[r+3]=t>>>24&255}}}function i(e){while(n<e)Object.defineProperty(t.prototype,n,r(n)),n++}t.prototype=Object.create(null);var n=0;return t}(),IDENTITY_MATRIX=[1,0,0,1,0,0],Util=PDFJS.Util=function(){function t(){}var n=["rgb(",0,",",0,",",0,")"];return t.makeCssRgb=function(t,r,i){return n[1]=t,n[3]=r,n[5]=i,n.join("")},t.transform=function(t,n){return[t[0]*n[0]+t[2]*n[1],t[1]*n[0]+t[3]*n[1],t[0]*n[2]+t[2]*n[3],t[1]*n[2]+t[3]*n[3],t[0]*n[4]+t[2]*n[5]+t[4],t[1]*n[4]+t[3]*n[5]+t[5]]},t.applyTransform=function(t,n){var r=t[0]*n[0]+t[1]*n[2]+n[4],i=t[0]*n[1]+t[1]*n[3]+n[5];return[r,i]},t.applyInverseTransform=function(t,n){var r=n[0]*n[3]-n[1]*n[2],i=(t[0]*n[3]-t[1]*n[2]+n[2]*n[5]-n[4]*n[3])/r,s=(-t[0]*n[1]+t[1]*n[0]+n[4]*n[1]-n[5]*n[0])/r;return[i,s]},t.getAxialAlignedBoundingBox=function(n,r){var i=t.applyTransform(n,r),s=t.applyTransform(n.slice(2,4),r),o=t.applyTransform([n[0],n[3]],r),u=t.applyTransform([n[2],n[1]],r);return[Math.min(i[0],s[0],o[0],u[0]),Math.min(i[1],s[1],o[1],u[1]),Math.max(i[0],s[0],o[0],u[0]),Math.max(i[1],s[1],o[1],u[1])]},t.inverseTransform=function(t){var n=t[0]*t[3]-t[1]*t[2];return[t[3]/n,-t[1]/n,-t[2]/n,t[0]/n,(t[2]*t[5]-t[4]*t[3])/n,(t[4]*t[1]-t[5]*t[0])/n]},t.apply3dTransform=function(t,n){return[t[0]*n[0]+t[1]*n[1]+t[2]*n[2],t[3]*n[0]+t[4]*n[1]+t[5]*n[2],t[6]*n[0]+t[7]*n[1]+t[8]*n[2]]},t.singularValueDecompose2dScale=function(t){var n=[t[0],t[2],t[1],t[3]],r=t[0]*n[0]+t[1]*n[2],i=t[0]*n[1]+t[1]*n[3],s=t[2]*n[0]+t[3]*n[2],o=t[2]*n[1]+t[3]*n[3],u=(r+o)/2,a=Math.sqrt((r+o)*(r+o)-4*(r*o-s*i))/2,f=u+a||1,l=u-a||1;return[Math.sqrt(f),Math.sqrt(l)]},t.normalizeRect=function(t){var n=t.slice(0);return t[0]>t[2]&&(n[0]=t[2],n[2]=t[0]),t[1]>t[3]&&(n[1]=t[3],n[3]=t[1]),n},t.intersect=function(n,r){function i(e,t){return e-t}var s=[n[0],n[2],r[0],r[2]].sort(i),o=[n[1],n[3],r[1],r[3]].sort(i),u=[];return n=t.normalizeRect(n),r=t.normalizeRect(r),s[0]===n[0]&&s[1]===r[0]||s[0]===r[0]&&s[1]===n[0]?(u[0]=s[1],u[2]=s[2],o[0]===n[1]&&o[1]===r[1]||o[0]===r[1]&&o[1]===n[1]?(u[1]=o[1],u[3]=o[2],u):!1):!1},t.sign=function(t){return t<0?-1:1},t.appendToArray=function(t,n){Array.prototype.push.apply(t,n)},t.prependToArray=function(t,n){Array.prototype.unshift.apply(t,n)},t.extendObj=function(t,n){for(var r in n)t[r]=n[r]},t.getInheritableProperty=function(t,n){while(t&&!t.has(n))t=t.get("Parent");return t?t.get(n):null},t.inherit=function(t,n,r){t.prototype=Object.create(n.prototype),t.prototype.constructor=t;for(var i in r)t.prototype[i]=r[i]},t.loadScript=function(t,n){var r=document.createElement("script"),i=!1;r.setAttribute("src",t),n&&(r.onload=function(){i||n(),i=!0}),document.getElementsByTagName("head")[0].appendChild(r)},t}(),PageViewport=PDFJS.PageViewport=function(){function t(e,t,n,r,i,s){this.viewBox=e,this.scale=t,this.rotation=n,this.offsetX=r,this.offsetY=i;var o=(e[2]+e[0])/2,u=(e[3]+e[1])/2,a,f,l,c;n%=360,n=n<0?n+360:n;switch(n){case 180:a=-1,f=0,l=0,c=1;break;case 90:a=0,f=1,l=1,c=0;break;case 270:a=0,f=-1,l=-1,c=0;break;default:a=1,f=0,l=0,c=-1}s&&(l=-l,c=-c);var h,p,d,v;a===0?(h=Math.abs(u-e[1])*t+r,p=Math.abs(o-e[0])*t+i,d=Math.abs(e[3]-e[1])*t,v=Math.abs(e[2]-e[0])*t):(h=Math.abs(o-e[0])*t+r,p=Math.abs(u-e[1])*t+i,d=Math.abs(e[2]-e[0])*t,v=Math.abs(e[3]-e[1])*t),this.transform=[a*t,f*t,l*t,c*t,h-a*t*o-l*t*u,p-f*t*o-c*t*u],this.width=d,this.height=v,this.fontScale=t}return t.prototype={clone:function(n){n=n||{};var r="scale"in n?n.scale:this.scale,i="rotation"in n?n.rotation:this.rotation;return new t(this.viewBox.slice(),r,i,this.offsetX,this.offsetY,n.dontFlip)},convertToViewportPoint:function(t,n){return Util.applyTransform([t,n],this.transform)},convertToViewportRectangle:function(t){var n=Util.applyTransform([t[0],t[1]],this.transform),r=Util.applyTransform([t[2],t[3]],this.transform);return[n[0],n[1],r[0],r[1]]},convertToPdfPoint:function(t,n){return Util.applyInverseTransform([t,n],this.transform)}},t}(),PDFStringTranslateTable=[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,728,711,710,729,733,731,730,732,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8226,8224,8225,8230,8212,8211,402,8260,8249,8250,8722,8240,8222,8220,8221,8216,8217,8218,8482,64257,64258,321,338,352,376,381,305,322,339,353,382,0,8364];PDFJS.createPromiseCapability=createPromiseCapability,function(){function o(e){this._status=t,this._handlers=[];try{e.call(this,this._resolve.bind(this),this._reject.bind(this))}catch(n){this._reject(n)}}if(globalScope.Promise){typeof globalScope.Promise.all!="function"&&(globalScope.Promise.all=function(e){var t=0,n=[],r,i,s=new globalScope.Promise(function(e,t){r=e,i=t});return e.forEach(function(e,s){t++,e.then(function(e){n[s]=e,t--,t===0&&r(n)},i)}),t===0&&r(n),s}),typeof globalScope.Promise.resolve!="function"&&(globalScope.Promise.resolve=function(e){return new globalScope.Promise(function(t){t(e)})}),typeof globalScope.Promise.reject!="function"&&(globalScope.Promise.reject=function(e){return new globalScope.Promise(function(t,n){n(e)})}),typeof globalScope.Promise.prototype.catch!="function"&&(globalScope.Promise.prototype.catch=function(e){return globalScope.Promise.prototype.then(undefined,e)});return}var t=0,n=1,r=2,i=500,s={handlers:[],running:!1,unhandledRejections:[],pendingRejectionCheck:!1,scheduleHandlers:function(n){if(n._status===t)return;this.handlers=this.handlers.concat(n._handlers),n._handlers=[];if(this.running)return;this.running=!0,setTimeout(this.runHandlers.bind(this),0)},runHandlers:function(){var t=1,i=Date.now()+t;while(this.handlers.length>0){var s=this.handlers.shift(),o=s.thisPromise._status,u=s.thisPromise._value;try{o===n?typeof s.onResolve=="function"&&(u=s.onResolve(u)):typeof s.onReject=="function"&&(u=s.onReject(u),o=n,s.thisPromise._unhandledRejection&&this.removeUnhandeledRejection(s.thisPromise))}catch(a){o=r,u=a}s.nextPromise._updateStatus(o,u);if(Date.now()>=i)break}if(this.handlers.length>0){setTimeout(this.runHandlers.bind(this),0);return}this.running=!1},addUnhandledRejection:function(t){this.unhandledRejections.push({promise:t,time:Date.now()}),this.scheduleRejectionCheck()},removeUnhandeledRejection:function(t){t._unhandledRejection=!1;for(var n=0;n<this.unhandledRejections.length;n++)this.unhandledRejections[n].promise===t&&(this.unhandledRejections.splice(n),n--)},scheduleRejectionCheck:function(){if(this.pendingRejectionCheck)return;this.pendingRejectionCheck=!0,setTimeout(function(){this.pendingRejectionCheck=!1;var t=Date.now();for(var n=0;n<this.unhandledRejections.length;n++)if(t-this.unhandledRejections[n].time>i){var r=this.unhandledRejections[n].promise._value,s="Unhandled rejection: "+r;r.stack&&(s+="\n"+r.stack),warn(s),this.unhandledRejections.splice(n),n--}this.unhandledRejections.length&&this.scheduleRejectionCheck()}.bind(this),i)}};o.all=function(t){function f(e){if(s._status===r)return;a=[],i(e)}var n,i,s=new o(function(e,t){n=e,i=t}),u=t.length,a=[];if(u===0)return n(a),s;for(var l=0,c=t.length;l<c;++l){var h=t[l],p=function(e){return function(t){if(s._status===r)return;a[e]=t,u--,u===0&&n(a)}}(l);o.isPromise(h)?h.then(p,f):p(h)}return s},o.isPromise=function(t){return t&&typeof t.then=="function"},o.resolve=function(t){return new o(function(e){e(t)})},o.reject=function(t){return new o(function(e,n){n(t)})},o.prototype={_status:null,_value:null,_handlers:null,_unhandledRejection:null,_updateStatus:function(t,i){if(this._status===n||this._status===r)return;if(t===n&&o.isPromise(i)){i.then(this._updateStatus.bind(this,n),this._updateStatus.bind(this,r));return}this._status=t,this._value=i,t===r&&this._handlers.length===0&&(this._unhandledRejection=!0,s.addUnhandledRejection(this)),s.scheduleHandlers(this)},_resolve:function(t){this._updateStatus(n,t)},_reject:function(t){this._updateStatus(r,t)},then:function(t,n){var r=new o(function(e,t){this.resolve=e,this.reject=t});return this._handlers.push({thisPromise:this,onResolve:t,onReject:n,nextPromise:r}),s.scheduleHandlers(this),r},"catch":function(t){return this.then(undefined,t)}},globalScope.Promise=o}();var StatTimer=function(){function t(e,t,n){while(e.length<n)e+=t;return e}function n(){this.started={},this.times=[],this.enabled=!0}return n.prototype={time:function(t){if(!this.enabled)return;t in this.started&&warn("Timer is already running for "+t),this.started[t]=Date.now()},timeEnd:function(t){if(!this.enabled)return;t in this.started||warn("Timer has not been started for "+t),this.times.push({name:t,start:this.started[t],end:Date.now()}),delete this.started[t]},toString:function(){var n,r,i=this.times,s="",o=0;for(n=0,r=i.length;n<r;++n){var u=i[n].name;u.length>o&&(o=u.length)}for(n=0,r=i.length;n<r;++n){var a=i[n],f=a.end-a.start;s+=t(a.name," ",o)+" "+f+"ms\n"}return s}},n}();PDFJS.createBlob=function(t,n){if(typeof Blob!="undefined")return new Blob([t],{type:n});var r=new MozBlobBuilder;return r.append(t),r.getBlob(n)},PDFJS.createObjectURL=function(){var t="ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/=";return function(n,r){if(!PDFJS.disableCreateObjectURL&&typeof URL!="undefined"&&URL.createObjectURL){var i=PDFJS.createBlob(n,r);return URL.createObjectURL(i)}var s="data:"+r+";base64,";for(var o=0,u=n.length;o<u;o+=3){var a=n[o]&255,f=n[o+1]&255,l=n[o+2]&255,c=a>>2,h=(a&3)<<4|f>>4,p=o+1<u?(f&15)<<2|l>>6:64,d=o+2<u?l&63:64;s+=t[c]+t[h]+t[p]+t[d]}return s}}(),MessageHandler.prototype={on:function(t,n,r){var i=this.actionHandler;i[t]&&error('There is already an actionName called "'+t+'"'),i[t]=[n,r]},send:function(t,n,r){var i={action:t,data:n};this.postMessage(i,r)},sendWithPromise:function(t,n,r){var i=this.callbackIndex++,s={action:t,data:n,callbackId:i},o=createPromiseCapability();this.callbacksCapabilities[i]=o;try{this.postMessage(s,r)}catch(u){o.reject(u)}return o.promise},postMessage:function(e,t){t&&this.postMessageTransfers?this.comObj.postMessage(e,t):this.comObj.postMessage(e)}},define("jpx",function(){});var cornerstoneWADOImageLoader=function(e,t,n){"use strict";function r(e){return e==="RGB"||e==="PALETTE COLOR"||e==="YBR_FULL"||e==="YBR_FULL_422"||e==="YBR_PARTIAL_422"||e==="YBR_PARTIAL_420"||e==="YBR_RCT"?!0:!1}function i(e,t,i){i===undefined&&(i=0);var s=e.string("x00280004"),o=r(s);return o===!1?n.makeGrayscaleImage(t,e,e.byteArray,s,i):n.makeColorImage(t,e,e.byteArray,s,i)}function o(n){var r=e.Deferred(),o=n;o=o.substring(9);var u=o.indexOf("frame="),a;if(u!==-1){var f=o.substr(u+6);a=parseInt(f),o=o.substr(0,u-1)}if(a!==undefined&&s.hasOwnProperty(o)){var l=s[o],c=i(l,n,a);return c.then(function(e){r.resolve(e)},function(){r.reject()}),r}var h=new XMLHttpRequest;return h.open("get",o,!0),h.responseType="arraybuffer",h.onreadystatechange=function(e){if(h.readyState===4)if(h.status===200){var t=h.response,u=new Uint8Array(t),f=dicomParser.parseDicom(u);a!==undefined&&(s[o]=f);var l=i(f,n,a);l.then(function(e){r.resolve(e)},function(){r.reject()})}else r.reject()},h.onprogress=function(r){if(r.lengthComputable){var i=r.loaded,s=r.total,o=Math.round(i/s*100);e(t).trigger("CornerstoneImageLoadProgress",{imageId:n,loaded:i,total:s,percentComplete:o})}},h.send(),r}n===undefined&&(n={});var s={};return t.registerImageLoader("dicomweb",o),n}($,cornerstone,cornerstoneWADOImageLoader),cornerstoneWADOImageLoader=function(e){"use strict";function t(e,t){if(e===undefined)throw"decodeRGB: rgbBuffer must not be undefined";if(e.length%3!==0)throw"decodeRGB: rgbBuffer length must be divisble by 3";var n=e.length/3,r=0,i=0;for(var s=0;s<n;s++)t[i++]=e[r++],t[i++]=e[r++],t[i++]=e[r++],t[i++]=255}return e===undefined&&(e={}),e.decodeRGB=t,e}(cornerstoneWADOImageLoader),cornerstoneWADOImageLoader=function(e){"use strict";function t(e,t){if(e===undefined)throw"decodeRGB: ybrBuffer must not be undefined";if(e.length%3!==0)throw"decodeRGB: ybrBuffer length must be divisble by 3";var n=e.length/3,r=0,i=0;for(var s=0;s<n;s++){var o=e[r++],u=e[r++],a=e[r++];t[i++]=o+1.402*(a-128),t[i++]=o-.34414*(u-128)-.71414*(a-128),t[i++]=o+1.772*(u-128),t[i++]=255}}return e===undefined&&(e={}),e.decodeYBRFull=t,e}(cornerstoneWADOImageLoader),cornerstoneWADOImageLoader=function(e){"use strict";function t(e){var t=e.string("x00280030");if(t&&t.length>0){var n=t.split("\\");return{row:parseFloat(n[0]),column:parseFloat(n[1])}}return{row:undefined,column:undefined}}return e===undefined&&(e={}),e.getPixelSpacing=t,e}(cornerstoneWADOImageLoader),cornerstoneWADOImageLoader=function(e){"use strict";function t(e){var t={intercept:0,slope:1},n=e.floatString("x00281052"),r=e.floatString("x00281053");return n&&(t.intercept=n),r&&(t.slope=r),t}return e===undefined&&(e={}),e.getRescaleSlopeAndIntercept=t,e}(cornerstoneWADOImageLoader),cornerstoneWADOImageLoader=function(e){"use strict";function t(e){var t={windowCenter:undefined,windowWidth:undefined},n=e.floatString("x00281050"),r=e.floatString("x00281051");return n&&(t.windowCenter=n),r&&(t.windowWidth=r),t}return e===undefined&&(e={}),e.getWindowWidthAndCenter=t,e}(cornerstoneWADOImageLoader),cornerstoneWADOImageLoader=function(e,t,n){"use strict";function s(e){return o(String.fromCharCode.apply(null,Array.prototype.slice.apply(new Uint8Array(e))))}function o(e){var t;try{return decodeURIComponent(escape(e))}catch(n){t=n;if(t instanceof URIError)return e;throw t}}function u(t,i,o,u,a,f){r.height=a,r.width=u;var l=t.elements.x7fe00010,c=l.dataOffset,h=t.string("x00020010"),p=u*a*3,d=c+f*p,v,m=r.getContext("2d"),g=m.createImageData(u,a),y=e.Deferred();if(o==="RGB")return v=new Uint8Array(i.buffer,d,p),n.decodeRGB(v,g.data),y.resolve(g),y;if(o==="YBR_FULL")return v=new Uint8Array(i.buffer,d,p),n.decodeYBRFull(v,g.data),y.resolve(g),y;if(o==="YBR_FULL_422"&&h==="1.2.840.10008.1.2.4.50"){v=dicomParser.readEncapsulatedPixelData(t,t.elements.x7fe00010,f);var b=new Blob([v],{type:"image/jpeg"}),w=new FileReader;return w.readAsBinaryString===undefined?w.readAsArrayBuffer(b):w.readAsBinaryString(b),w.onload=function(){var e=new Image;e.onload=function(){m.drawImage(this,0,0),g=m.getImageData(0,0,u,a),y.resolve(g)},e.onerror=function(e){y.reject()},w.readAsBinaryString===undefined?e.src="data:image/jpeg;base64,"+window.btoa(s(w.result)):e.src="data:image/jpeg;base64,"+window.btoa(w.result)},y}throw"no codec for "+o}function a(s,o,a,f,l){var c=n.getPixelSpacing(o),h=o.uint16("x00280010"),p=o.uint16("x00280011"),d=n.getRescaleSlopeAndIntercept(o),v=4,m=h*p,g=m*v,y=n.getWindowWidthAndCenter(o),b=e.Deferred(),w=u(o,a,f,p,h,l);return w.then(function(e){function n(){return e.data}function u(){return e}function a(){if(i===s)return r;r.height=h,r.width=p;var t=r.getContext("2d");return t.putImageData(e,0,0),i=s,r}var f={imageId:s,minPixelValue:0,maxPixelValue:255,slope:d.slope,intercept:d.intercept,windowCenter:y.windowCenter,windowWidth:y.windowWidth,render:t.renderColorImage,getPixelData:n,getImageData:u,getCanvas:a,rows:h,columns:p,height:h,width:p,color:!0,columnPixelSpacing:c.column,rowPixelSpacing:c.row,data:o,invert:!1,sizeInBytes:g};f.windowCenter===undefined&&(f.windowWidth=255,f.windowCenter=128),b.resolve(f)},function(){b.reject()}),b}n===undefined&&(n={});var r=document.createElement("canvas"),i="";return n.makeColorImage=a,n}($,cornerstone,cornerstoneWADOImageLoader),cornerstoneWADOImageLoader=function(e,t,n){"use strict";function r(e){var t=e.uint16("x00280103"),n=e.uint16("x00280100");if(t===0&&n===8)return 1;if(t===0&&n===16)return 2;if(t===1&&n===16)return 3}function i(e,t,n,r){var i=dicomParser.readEncapsulatedPixelData(e,e.elements.x7fe00010,r),s=new JpxImage;s.parse(i);var o=s.width,u=s.height;if(o!==t)throw"JPEG2000 decoder returned width of "+o+", when "+t+" is expected";if(u!==n)throw"JPEG2000 decoder returned width of "+u+", when "+n+" is expected";var a=s.componentsCount;if(a!==1)throw"JPEG2000 decoder returned a componentCount of "+a+", when 1 is expected";var f=s.tiles.length;if(f!==1)throw"JPEG2000 decoder returned a tileCount of "+f+", when 1 is expected";var l=s.tiles[0],c=l.items;return c}function s(e,t,n,i){var s=r(e),o=e.elements.x7fe00010,u=o.dataOffset,a=t*n,f=0;if(s===1)return f=u+i*a,new Uint8Array(e.byteArray.buffer,f,a);if(s===2)return f=u+i*a*2,new Uint16Array(e.byteArray.buffer,f,a);if(s===3)return f=u+i*a*2,new Int16Array(e.byteArray.buffer,f,a)}function o(e,t,n,r){var o=e.string("x00020010");return o==="1.2.840.10008.1.2.4.90"||o==="1.2.840.10008.1.2.4.91"?i(e,t,n,r):s(e,t,n,r)}function u(e){var t=r(e);if(t===1)return 1;if(t===2||t===3)return 2;throw"unknown pixel format"}function a(e){var t=65535,n=-32768,r=e.length,i=e;for(var s=0;s<r;s++){var o=i[s];t=Math.min(t,o),n=Math.max(n,o)}return{min:t,max:n}}function f(r,i,s,f,l){function S(){return w}var c=n.getPixelSpacing(i),h=i.uint16("x00280010"),p=i.uint16("x00280011"),d=n.getRescaleSlopeAndIntercept(i),v=u(i),m=h*p,g=m*v,y=f==="MONOCHROME1",b=n.getWindowWidthAndCenter(i),w=o(i,p,h,l),E=a(w),x={imageId:r,minPixelValue:E.min,maxPixelValue:E.max,slope:d.slope,intercept:d.intercept,windowCenter:b.windowCenter,windowWidth:b.windowWidth,render:t.renderGrayscaleImage,getPixelData:S,rows:h,columns:p,height:h,width:p,color:!1,columnPixelSpacing:c.column,rowPixelSpacing:c.row,data:i,invert:y,sizeInBytes:g};if(x.windowCenter===undefined){var T=x.maxPixelValue*x.slope+x.intercept,N=x.minPixelValue*x.slope+x.intercept;x.windowWidth=T-N,x.windowCenter=(T+N)/2}var C=e.Deferred();return C.resolve(x),C}return n===undefined&&(n={}),n.makeGrayscaleImage=f,n}($,cornerstone,cornerstoneWADOImageLoader);define("cornerstoneWADOImageLoader",function(){}),require(["jquery","hammerjs","cornerstone","cornerstoneMath","cornerstoneTools","dicomParser","cornerstoneWebImageLoader","jpx","cornerstoneWADOImageLoader"],function(e,t,n){jQuery(t).ready(function(e){var n,r=t.getElementsByTagName("script"),i=/.*cornerstoneWidget\.([^/]+\.)?js/,s=[];for(var o=0;o<r.length;o++){var u=r[o];if(u.src.match(i)&&s.indexOf(u)<0){s.push(u),console.log("Identified embeded script with info: %o",u.src);var a=u.src.split("?"),f=a[a.length-1];console.log(f),n=f.replace("image=","")}}var l=t.getElementById("cornerstoneWidget-container");cornerstone.enable(l),cornerstone.loadImage(n).then(function(e){cornerstone.displayImage(l,e),cornerstoneTools.mouseInput.enable(l),cornerstoneTools.mouseWheelInput.enable(l),cornerstoneTools.wwwc.activate(l,1),cornerstoneTools.pan.activate(l,2),cornerstoneTools.zoom.activate(l,4),cornerstoneTools.zoomWheel.activate(l)})})}(window,document)),define("src/widget.js",function(){});