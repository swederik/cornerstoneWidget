require(['jquery', 'hammerjs',
         'cornerstone', 'cornerstoneMath',
         'cornerstoneTools', 'dicomParser',
         'cornerstoneWebImageLoader',
         'jpx', 'cornerstoneWADOImageLoader'], function(window, document, undefined) {

    jQuery(document).ready(function($) {

        var imageId;

        // This is for later adaption to allow for multiple embeds...
        var scriptElements = document.getElementsByTagName('script');
        var regexp = /.*cornerstoneWidget\.([^/]+\.)?js/;
        var foundScriptElements = [];

        for(var i = 0; i < scriptElements.length; i++) {
            var scriptElement = scriptElements[i];

            // Make sure the element matches our regexp
            // and is not currently in the list of known elements
            if(scriptElement.src.match(regexp) && foundScriptElements.indexOf(scriptElement) < 0) {
              foundScriptElements.push(scriptElement);
              console.log('Identified embeded script with info: %o', scriptElement.src);
              var splitSrc = scriptElement.src.split("?");
              var params = splitSrc[splitSrc.length-1];
              console.log(params);
              imageId = params.replace("image=", "");
            }
        }

        var element = document.getElementById('cornerstoneWidget-container');
        cornerstone.enable(element);
        cornerstone.loadImage(imageId).then(function(image) {
            cornerstone.displayImage(element, image);
            cornerstoneTools.mouseInput.enable(element);
            cornerstoneTools.mouseWheelInput.enable(element);
            // Enable all tools we want to use with this element
            cornerstoneTools.wwwc.activate(element, 1); // ww/wc is the default tool for left mouse button
            cornerstoneTools.pan.activate(element, 2); // pan is the default tool for middle mouse button
            cornerstoneTools.zoom.activate(element, 4); // zoom is the default tool for right mouse button
            cornerstoneTools.zoomWheel.activate(element); // zoom is the default tool for middle mouse wheel
        });
    });
}(window, document));