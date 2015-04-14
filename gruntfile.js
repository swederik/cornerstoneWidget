module.exports = function(grunt) {

    // Project configuration.
    grunt.initConfig({
        pkg: grunt.file.readJSON('package.json'),
        clean: {
            default: {
                src: [
                    'dist'
                ]
            }
        },
        jshint: {
            files: [
                'src/**/*.js'
            ],
            options: {
                    evil: true, // Suppress warnings about document.write
                    shadow: true,
                    globals: {
                        jQuery: true,
                        cornerstone: true
                    },
            }
        },
        requirejs: {
          compile: {
            options: {
              baseUrl: ".",
              mainConfigFile: "config.js",
              name: "src/widget.js",
              out: "build/optimized.js"
            }
          }
        },
        concat: {
            dist: {
                options: {
                    stripBanners: true,
                    banner: '/*! <%= pkg.name %> - v<%= pkg.version %> - ' +
                        '<%= grunt.template.today("yyyy-mm-dd") %> ' +
                        '| (c) 2015 Erik Ziegler | https://github.com/swederik/cornerstoneWidget */\n'
                },
                src : ['node_modules/requirejs/require.js', 'build/optimized.js'],
                dest: 'dist/cornerstoneWidget.js'
            }
        },
        watch: {
            scripts: {
                files: ['src/**/*.js', 'test/*.js'],
                tasks: ['jshint', 'concat:dist', 'requirejs']
            }
        },

    });

    require('load-grunt-tasks')(grunt);

    grunt.registerTask('buildAll', ['jshint', 'concat:dist', 'requirejs']);
    grunt.registerTask('default', ['clean', 'buildAll']);
};


// Release process:
//  1) Update version numbers
//  2) do a build (needed to update dist versions with correct build number)
//  3) commit changes
//      git commit -am "Changes...."
//  4) tag the commit
//      git tag -a 0.1.0 -m "Version 0.1.0"
//  5) push to github
//      git push origin master --tags
