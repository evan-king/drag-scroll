// Drag Scroll extension by Evan King (evan@bluespurs.com)
//
// See license.txt for more information (GPL)

function dragscrollExtensionNS() {

this.dsInit=dsInit;
this.dsClose=dsClose;
this.clearDragInfo=clearDragInfo; 
this.dsToggleKeyHandler=dsToggleKeyHandler;
this.dsToggle=dsToggle;
this.dsOnItem=dsOnItem;
this.dsShowOptions=dsShowOptions;
this.openBlacklist=openBlacklist;

const dsVERSION = "1.0.0", dsWindows = 0, dsMac = 1, dsOther = 2, 
	  dsLeft = 0, dsMiddle = 1, dsRight = 2,
	  dsQTdisabled = -2, dsQTonHover = -1, dsQTonDrag = 0, dsQTonClick = 1, dsQTonDoubleClick = 2;
const dsPrefListener = {
	domain: "extensions.dragscroll.",
	observe: function(subject, topic, prefName) {
		dsInit();
	}
}
const domWindowUtils = window.QueryInterface(Ci.nsIInterfaceRequestor).getInterface(Ci.nsIDOMWindowUtils);
const dsClipboardHelper = Components.classes["@mozilla.org/widget/clipboardhelper;1"].getService(Components.interfaces.nsIClipboardHelper); 
const dsPrompts = Components.classes["@mozilla.org/embedcomp/prompt-service;1"].getService(Components.interfaces.nsIPromptService);
const dsPrefService = Components.classes["@mozilla.org/preferences-service;1"].getService(Components.interfaces.nsIPrefService);
const DS_UUID = "dragscroll@honoredsoft.com"; 
const httpProtocolHandler = Components.classes["@mozilla.org/network/protocol;1?name=http"].getService(Components.interfaces.nsIHttpProtocolHandler);
const appInfo = Components.classes["@mozilla.org/xre/app-info;1"].getService(Components.interfaces.nsIXULAppInfo);
const versionChecker = Components.classes["@mozilla.org/xpcom/version-comparator;1"].getService(Components.interfaces.nsIVersionComparator);

var dsPlatform, dsStrings, dsContentArea, dsRenderingArea, dsAppContent, dsCIbox, dsCIbrowser, dsMouseWin=null, dsScrollObj,
	dsStartX, dsStartY, dsLastX, dsLastY, dsLastMoveX, dsLastMoveY, dsLastTime, dsLastVel, dsshortdT, dsshortdX,
	dsOn, dsVer, dsFirstCall=true, dsStdCursor, dsDragCursor, dsDragInc, dsMult, dsReverse, dsSBMode, dsButton, 
	dsQTonCnt, dsQToffCnt, dsQTonTime, dsQToffTime, dsTogKey, dsUseCtrl, dsUseAlt, dsUseShift, dsMoveTime, 
	dsFlickOn, dsFlickSpeed, dsFlickTimeLimit, dsFlickWholePage, dsFlickHoriz, dsSavedDown, dsInQT, dsWasScrolling, 
	dsDragDoc, dsTO, dsTOqtOn=null, dsTOqtOff=null, dsCopyOnQToff, dsDownStr, dsStrToCpy=null, dsOnText, dsStrict, 
	dsBlacklist = new dsFilter(), dsTextDoesntCount = new dsFilter(), dsCountsAsText = new dsFilter(),
	dsScrollLoopInterval, dsScrollLastLoop, dsScrollLastMoveLoop, dsScrollToGo, dsSmoothStop, dsSmoothFactor, dsScrollHoriz,
	dsScrollVel, dsScrollVelMult, dsScrollMaxInterval, dsScrollFrictionMult, 
	dsDists = new dsStack(50), dsVels = new dsStack(50), dsTimes = new dsStack(50), 
	dsMomOn, dsMomExtent, dsMomVariation, dsMomFriction, 
	dsPref = dsPrefService.getBranch("extensions.dragscroll."), dsPrefRoot = dsPrefService.getBranch(null),
	dsPbi = dsPrefRoot.QueryInterface(Components.interfaces.nsIPrefBranchInternal);


function mod(m,n) {	return (m>=0?m%n:(n-((n-m)%n))%n); } // mod should always be positive!
function sgn(n) { if (n<0) return -1; if (n>0) return 1; return 0; }

// dsFilter
function dsFilter() 
{
	this.locFilters = []; this.elFilters = []; this.specialFilter=[];
	this.linksBLon = false;
	
	this.clearFilters = function() {
		this.locFilters = []; this.elFilters = []; this.specialFilter = [];
		this.linksBLon = false;
	}
	this.addFromString = function(textin) {
		var objin = JSON.parse(textin);
		for (var i=0; i<objin.length; i++) {			
			if (objin[i].on=="true") {
				// process adblock plus style domain filter rules
				var tmp = objin[i].url.replace(/\^\|$/, "^")       // remove anchors following separator placeholder
										 .replace(/\W/g, "\\$&")    // escape special symbols
										 .replace(/\\\*/g, ".*")      // replace wildcards by .*
										 // process separator placeholders (all ANSI charaters but alphanumeric characters and _%.-)
										 .replace(/\\\^/g, "(?:[\\x00-\\x24\\x26-\\x2C\\x2F\\x3A-\\x40\\x5B-\\x5E\\x60\\x7B-\\x80]|$)")
										 .replace(/^\\\|\\\|/, "^[\\w\\-]+:\\/+(?!\\/)(?:[^.\\/]+\\.)*?") // process extended anchor at expression start
										 .replace(/^\\\|/, "^")       // process anchor at expression start
										 .replace(/\\\|$/, "$");      // process anchor at expression end
				this.locFilters.push(new RegExp(tmp,"i"));
				if (objin[i].elem=="*") {
					this.elFilters.push("*");
				} else {
					this.elFilters.push(objin[i].elem+","+objin[i].elem.replace(/,/g," *,")+" *");
				}
				if (objin[i].id == "links") this.linksBLon = true;	// this is pretty hacky. might be nice to add computed style selectors to blacklists, but maybe not worth the effort
			}
		}
	}
	this.setFromString = function(textin,specialin) {		
		this.clearFilters();
		this.addFromString(textin);
		if (specialin!="") {
			this.specialFilter=new RegExp(specialin,"i");
		}
	}
	this.test = function(el) {
		if (!(el instanceof Element)) return false;
		
		if (this.specialFilter.test) {
			if (this.specialFilter.test(el.nodeName)) return true;
		}
		
		var loc = el.ownerDocument.documentURI.split("?",1); loc=loc[0];
		
		for (var i=0; i<this.locFilters.length; i++) {
			if (this.locFilters[i].test(loc)) {
				try { 
					if (el.mozMatchesSelector(this.elFilters[i])) {
						return true;
					}
				} catch(err) { }
			}
		}
		return false;
	}
}	// end dsFilter

// a dsStack is an object that holds a stack of data and data analysis routines-- used to 
// hold/analyze user's dragging behavior for momentum implementation. emphasis is on fast 
// writing to data struct during the dragging in order to maximize performance
function dsStack(k) {
	this.entries = new Array(k);
	this.length=0; this.next=0; this.n=k;
	
	this.add = function(x) {
		this.entries[this.next]=x; 
		if (this.length < this.n) this.length++;
		this.next=mod(this.next+1,this.n);
	}
	this.clear = function() { this.length=0; }
	this.val = function(m) { return this.entries[mod(this.next-1-m,this.n)]; }
	this.sum = function () { var i; var tot=0; for (i=0; i<this.length; i++) tot+=this.val(i); return tot; }
	this.avg = function(m,N) { 
		var i; var tot=0; N=Math.min(N,this.length-1);
		for (i=m; i<=N; i++) tot+=this.val(i); 
		return tot/(N-m+1); 
	}
	this.biasedAvg = function(m,N) {  // biased to lower values to reduce large outliers
		var s=0, c=0, i, tot=1.0; N=Math.min(N,this.length-1);
		for (i=m; i<=N; i++) tot*=this.val(i); 
		tot = Math.pow(tot,1/(N-m+1)); 
		for (i=m; i<=N; i++) {
			if (this.val(i) < tot) { s+=this.val(i); c++; }
		}
		return (s>0?s/c:tot);		
	}
	this.sumWithin = function(D) { 
		var dist=0, i; 
		for (i=0; (dist<D)&&(i<this.length); i++) dist+=this.val(i);
		return i-1;
	}
	this.maxabs = function(m,N) { 
		var i; var v=Math.abs(this.val(m)); N=Math.min(N,this.length-1);
		for (i=m; i<=N; i++) v=Math.max(v,Math.abs(this.val(i))); 
		return v; 
	}
	this.minabs = function(m,N) { 
		var i; var v=Math.abs(this.val(m)); N=Math.min(N,this.length-1);
		for (i=m; i<=N; i++) v=Math.min(v,Math.abs(this.val(i))); 
		return v; 
	}
}	// end dsStack

function dsShowOptions(intro) {
	if (intro) {
		window.openDialog("chrome://dragscroll/content/dsIntro.xul", "dsIntro", "chrome=yes,dialog=yes,resizable=yes");
	} else {
		window.openDialog("chrome://dragscroll/content/dsPrefs.xul", "dsPrefs", "chrome=yes,dialog=yes,resizable=yes");
	}
}

function openBlacklist(inpar,edits) {
	window.openDialog("chrome://dragscroll/content/dsBL.xul", "dsBL", "chrome=yes,dialog=yes,resizable=yes",inpar,edits);
}

function dsInit()
{
	dsInQT=false; dsWasScrolling=false; dsSavedDown = null; 

	// first time initializing G&D since the window was loaded
	if (dsFirstCall) {
		// identify OS (for right-click handling)
		var p = httpProtocolHandler.platform.toLowerCase();
		if (p.indexOf('win') != -1) dsPlatform = dsWindows;
		else if (p.indexOf('mac') != -1) dsPlatform = dsMac;
		else dsPlatform = dsOther;			
		dsFirstCall=false;		
		dsStrings = document.getElementById("bundle_ds");
		window.addEventListener("customizationchange", dsUpdateButton, false);
		dsVer = dsPrefRoot.getCharPref("extensions.dragscroll-version");
		dsPrefRoot.setCharPref("extensions.dragscroll-version", dsVERSION); 
		// new install or version update
		if (dsVer != dsVERSION) {
			if (dsVer=="0.0.0") try { dsVer = dsPrefRoot.getCharPref("dragscroll-version"); } catch(err) { } 	
			dsVer=parseFloat(dsVer.substr(0,3));
			// new install or upgrade from very old install: run wizard
			if (dsVer<2.8) {		
				dsShowOptions(true);
			} else {					
				// there has been a significant change to preferences, etc, since last version: notify user
				var nb = gBrowser.getNotificationBox();
				var buttons = [{label: dsStrings.getAttribute("preftitle")+"...", accessKey: null,
								popup: null, callback: function(notif,butdesc) { dsShowOptions(false); } }]; 
				if (dsVer<3.1) convertPrefs();
				if (dsVer<3.2) {
					nb.appendNotification(dsStrings.getString("update.hoverchange"), 'ds-updated',
								'chrome://dragscroll/skin/dragscroll32.png', nb.PRIORITY_INFO_MEDIUM, buttons);
				}
			}
		}		
		updateHiddenBLs();
		dsPbi.addObserver(dsPrefListener.domain, dsPrefListener, false);
	}

	try { document.getElementById("ds-options").setAttribute("hidden",!dsPref.getBoolPref("toolsMenuEntry")) } catch(err) { }
	try { document.getElementById("ds-toggle-option").setAttribute("hidden",!dsPref.getBoolPref("toolsMenuEntry")) } catch(err) { }

	dsOn = dsPref.getBoolPref("on");
	dsTogKey = dsPref.getIntPref("togKey");
	dsUseCtrl = dsPref.getBoolPref("useCtrl");
	dsUseAlt = dsPref.getBoolPref("useAlt");
	dsUseShift = dsPref.getBoolPref("useShift");
	dsDragInc = parseFloat(dsPref.getCharPref("dragInc"));
	dsMult = parseFloat(dsPref.getCharPref("mult"));
	dsReverse = (dsPref.getBoolPref("reverse")?(-1):(1));
	dsSBMode = dsPref.getBoolPref("sbmode");
	dsStdCursor = dsPref.getCharPref("grabCursor");
	if (dsPref.getBoolPref("samecur")) dsDragCursor = dsStdCursor;
	else dsDragCursor = dsPref.getCharPref("grabbingCursor");
	// Fx27+ silently removes "-moz-" prefix from grab, grabbing cursors; must account for this here
	if(versionChecker.compare(appInfo.version, "27.0") >= 0) {
		dsStdCursor = dsStdCursor.replace(/^-moz-grab/,"grab");
		dsDragCursor = dsDragCursor.replace(/^-moz-grab/,"grab");
	}
	dsFlickOn = dsPref.getBoolPref("flickon");
	dsFlickHoriz = dsPref.getIntPref("flickhoriz");
	dsFlickSpeed = parseFloat(dsPref.getCharPref("flickspeed_ppms"));
	dsFlickTimeLimit = parseFloat(dsPref.getCharPref("flicktimelimit"));
	dsFlickWholePage = (dsPref.getIntPref("flickwhole")==-1);
	dsMomOn = dsPref.getBoolPref("momOn");
	dsMomVariation = parseFloat(dsPref.getCharPref("momVariation"));
	dsMomExtent = parseFloat(dsPref.getCharPref("momExtent")); 
	dsMomFriction = parseFloat(dsPref.getCharPref("momFriction"));
	dsSmoothStop = dsPref.getBoolPref("smoothStop");
	dsButton = dsPref.getIntPref("button");
	dsQTonCnt = (dsPref.getBoolPref("qtOn")?dsPref.getIntPref("qtOnCnt"):dsQTdisabled);
	dsQToffCnt = dsPref.getIntPref("qtOffCnt");
	dsQTonTime = parseFloat(dsPref.getCharPref("qtOnTime"));
	dsQToffTime = parseFloat(dsPref.getCharPref("qtOffTime"));
	dsCopyOnQToff = dsPref.getBoolPref("qtOffCopy");
	dsStrict = dsPref.getBoolPref("strict");
	dsshortdT= dsPref.getIntPref("shortdT");
	dsshortdX = dsPref.getIntPref("shortdX");
	dsBlacklist.setFromString(dsPref.getCharPref("blacklist"),dsPref.getCharPref("specialBL"));
	try { dsBlacklist.addFromString(dsPref.getCharPref("hiddenBL"+String(dsPref.getIntPref("button")))); } catch(err) { }
	dsTextDoesntCount.setFromString(dsPref.getCharPref("textdoesntcount"),"");
	dsCountsAsText.setFromString(dsPref.getCharPref("countsastext"),"");
	
	//*** maybe clean up or unify these... do we need three?
	dsContentArea = document.getElementById("content");	// tab browser, for tab selection events
	if (!dsContentArea) return;
	dsRenderingArea = document.getElementById("content").mPanelContainer;	// tabpanels 
	if (!dsRenderingArea) return;
	dsAppContent = document.getElementById("appcontent"); 	// box holding tab browser and misc
	if (!dsAppContent) return;
	// for Cool Iris, if installed
	dsCIbox = document.getElementById("cooliris-preview-overlay");	// plays role of appcontent
	if (dsCIbox) dsCIbrowser = dsCIbox.getPreviewFrame();	// plays role of tabpanels

	// clean up any old listeners, etc.
	if (dsScrollIntervalObj != null) {
		window.clearInterval(dsScrollIntervalObj); 
		dsScrollIntervalObj = null;
	}
	dsRenderingArea.removeEventListener("mousedown", dsDownHandler, true);
	dsAppContent.removeEventListener("mousedown",dsDownPreempt, true);
	dsRenderingArea.removeEventListener("click",dsClickHandler, true);
	dsAppContent.removeEventListener("DOMContentLoaded", dsLoad, true);
	dsAppContent.removeEventListener("click",dsClickPreempt, true);
	dsContentArea.removeEventListener("select", dsTabSelect, false);
	dsRenderingArea.removeEventListener("contextmenu", dsContextMenuPreempt, true);
	dsSetClearMousePos(false);
	dsSetClearContextListener(false);
	if (dsCIbox) {
		dsCIbrowser.removeEventListener("mousedown", dsDownHandler, true);
		dsCIbox.removeEventListener("mousedown",dsDownPreempt, true);
		dsCIbrowser.removeEventListener("click",dsClickHandler, true);
		dsCIbox.removeEventListener("click",dsClickPreempt, true);
		dsCIbox.removeEventListener("DOMContentLoaded", dsLoad, true);
	}
	window.removeEventListener("mouseup", dsUpHandler, true);
	window.removeEventListener("mousedown", dsUpHandler, true);
	window.removeEventListener("mousemove", dsMoveScrollBar, true);
	window.removeEventListener("DOMContentLoaded", dsUpHandler, true);
	window.removeEventListener("mousedown", dsManageMousePos, true);
	window.removeEventListener("mouseup", dsManageMousePos, true);
	window.removeEventListener("dragstart", dsManageMousePos, true);
	window.removeEventListener("dragend", dsManageMousePos, true);

	// Add the appropriate listeners, etc, if extension is enabled
	if (dsOn) { 
		dsRenderingArea.addEventListener("mousedown", dsDownHandler, true);
		dsAppContent.addEventListener("mousedown",dsDownPreempt, true);
		dsRenderingArea.addEventListener("click",dsClickHandler, true);
		dsAppContent.addEventListener("click",dsClickPreempt, true);
		dsAppContent.addEventListener("DOMContentLoaded", dsLoad, true);		
		if (dsCIbox) {
			dsCIbrowser.addEventListener("mousedown", dsDownHandler, true);
			dsCIbox.addEventListener("mousedown",dsDownPreempt, true);
			dsCIbrowser.addEventListener("click",dsClickHandler, true);
			dsCIbox.addEventListener("click",dsClickPreempt, true);
			dsCIbox.addEventListener("DOMContentLoaded", dsLoad, true);
		}
		dsSetClearMousePos(true);
		dsSetClearContextListener(true);	
		window.addEventListener("mousedown", dsManageMousePos, true);
		window.addEventListener("mouseup", dsManageMousePos, true);
		window.addEventListener("dragstart", dsManageMousePos, true);
		window.addEventListener("dragend", dsManageMousePos, true);
	}	
	dsContentArea.addEventListener("select", dsTabSelect, false);	// even when ext disabled (ensures proper mouse cursors)
	dsUpdateBrowser();
}

function dsSetClearContextListener(set) {
	if (dsPlatform != dsWindows && dsButton==dsRight) {	
		if (set) {
			dsRenderingArea.addEventListener("contextmenu", dsContextMenuPreempt, true);
			if (dsCIbox) dsCIbrowser.addEventListener("contextmenu", dsContextMenuPreempt, true);
		} else {
			dsRenderingArea.removeEventListener("contextmenu", dsContextMenuPreempt, true);
			if (dsCIbox) dsCIbrowser.removeEventListener("contextmenu", dsContextMenuPreempt, true);
		}
	}
}

// Always attached to window when G&D is on. Used to remove mouse-movement listeners during drags, etc, 
// both for performance and to avoid weirdness during text selection
function dsManageMousePos(e) {
	if (["mousedown","dragstart"].indexOf(e.type) > -1) dsSetClearMousePos(false);
	if (["mouseup","dragend"].indexOf(e.type) > -1) {
		dsSetClearMousePos(true);
		// do one check right away after drag ends even if mouse hasn't moved yet
		if (dsQTonCnt==dsQTonHover) dsCheckMousePos(e);
	}
}

function dsSetClearMousePos(set) {
	if (!set) {
		dsRenderingArea.removeEventListener("mousemove",dsCheckMousePos,true);
		dsRenderingArea.removeEventListener("mouseout",dsCheckMousePos,true);
		if (dsCIbox) {
			dsCIbox.removeEventListener("mousemove",dsCheckMousePos,true);
			dsCIbox.removeEventListener("mouseout",dsCheckMousePos,true);	
		}
		if (dsTOqtOn != null) {
			window.clearTimeout(dsTOqtOn);
			dsTOqtOn = null;
		}
		if (dsTOqtOff != null) {
			window.clearTimeout(dsTOqtOff);
			dsTOqtOff = null;
		}
	} else {
		if (dsQTonCnt==dsQTonHover) {
			dsRenderingArea.addEventListener("mousemove",dsCheckMousePos,true);
			dsRenderingArea.addEventListener("mouseout",dsCheckMousePos,true);
			if (dsCIbox) {
				dsCIbox.addEventListener("mousemove",dsCheckMousePos,true);
				dsCIbox.addEventListener("mouseout",dsCheckMousePos,true);
			}
		}
	}
}

// attached on mousemove and mouseout when using hover TextToggle
// explicitly called with a mouseup/dragend argument by dsManageMousePos on drag end
function dsCheckMousePos(e) {
	// Bail out if we're in the middle of scrolling (for performance and to avoid weirdness)
	if (dsScrollIntervalObj != null) return;
	
	dsMouseWin = e.originalTarget.ownerDocument.defaultView;
	var mouseOnText=false;
	if (["mousemove","mouseup","dragend"].indexOf(e.type) > -1) {
		try { 
			mouseOnText = (e.explicitOriginalTarget.nodeType==document.TEXT_NODE || dsCountsAsText.test(e.target)); 
		} catch(err) {}
	}
	
	if (mouseOnText) {
		if (dsInQT && dsTOqtOff!=null) {
			window.clearTimeout(dsTOqtOff);
			dsTOqtOff = null;
		}
		if (!dsInQT && dsTOqtOn==null) {
			dsTOqtOn = window.setTimeout(function(){ 
				dsTOqtOn = null;
				dsTextToggle(true); 
			},dsQTonTime);
		}	
	} else {
		if (dsInQT && dsTOqtOff==null) {
			dsTOqtOff = window.setTimeout(function(){ 
				try { 
					dsStrToCpy = dsMouseWin.getSelection().toString(); 
					dsMouseWin.goDoCommand("cmd_selectNone"); 
				} catch(err) { }
				dsMouseWin = null;
				dsTOqtOff = null;
				dsTextToggle(false); 
			},dsQToffTime);
		}
		if (!dsInQT && dsTOqtOn!=null) {
			window.clearTimeout(dsTOqtOn);
			dsTOqtOn = null;
		}
	}	
}

function dsTabSelect() 
{	
	dsUpdateBrowser();
}

function dsContextMenuPreempt(e)
{
	e.preventDefault(); e.stopPropagation();	
}

function dsClose()
{
	dsContentArea.removeEventListener("select", dsTabSelect, false);
	dsPbi.removeObserver(dsPrefListener.domain, dsPrefListener);
	dsAppContent.removeEventListener("mousedown",dsDownPreempt, true);
	try {
		dsRenderingArea.removeEventListener("mousedown", dsDownHandler, true);
		dsRenderingArea.removeEventListener("click",dsClickHandler, true);
	} catch(err) { } // may already be purged 
	dsAppContent.removeEventListener("DOMContentLoaded", dsLoad, true);
	dsAppContent.removeEventListener("click",dsClickPreempt, true);
	window.removeEventListener("mouseup", dsUpHandler, true);
	window.removeEventListener("mousedown", dsUpHandler, true);
	window.removeEventListener("mousemove", dsMoveScrollBar, true);
	window.removeEventListener("customizationchange", dsUpdateButton, false);
	window.removeEventListener("load", dsInit, false);
	dsSetClearMousePos(false);

	dsContentArea=null; dsRenderingArea=null; dsAppContent=null;
	dsScrollObj=null; dsPref=null;
	dsPrefRoot=null; 
	dsPbi=null;	
}

// The following two preempts are attached at Appcontent to catch clicks on scrollbars etc
// set some variables for later use by down and click handlers
function dsDownPreempt(e) 
{
	// dsWasScrolling keeps track of whether or not we were already scrolling from momentum/flick before the mousedown
	dsWasScrolling = (dsScrollIntervalObj != null);
	// dsSavedDown saves event details for later recreation if necessary, and it is nulled later if and only if the user dragged 
	dsSavedDown = {target:e.originalTarget,
					type:e.type,
					sx:e.screenX,
					sy:e.screenY, 
					x:Math.round((e.screenX-document.getElementById("main-window").boxObject.screenX)/domWindowUtils.screenPixelsPerCSSPixel),
					y:Math.round((e.screenY-document.getElementById("main-window").boxObject.screenY)/domWindowUtils.screenPixelsPerCSSPixel),
					button:e.button, 
					count:e.detail, 
					modifier:(e.altKey ? Ci.nsIDOMNSEvent.ALT_MASK : 0) | (e.ctrlKey ? Ci.nsIDOMNSEvent.CONTROL_MASK : 0) |
								(e.shiftKey ? Ci.nsIDOMNSEvent.SHIFT_MASK : 0) | (e.metaKey ? Ci.nsIDOMNSEvent.META_MASK : 0)
	};
	
	// here's where we need to deal w/left/right dragging on links -- textdoesntcount, also drag handlers....
	
	// dsOnText saves whether the mousedown happened "on text" for the purposes of click- or drag-driven quick toggles. 
	// "on text" means: text node inside an HTML element that isn't in the "doesn't count" blacklist; anything styled with a 
	// link-style "pointer" cursor is ignored to avoid triggering when a link is clicked; anything in the "counts as text" blacklist 
	// also counts as text (e.g. INPUT boxes, etc)
	var pointercur = (e.target.ownerDocument.defaultView.getComputedStyle(e.target, "").getPropertyValue("cursor")=="pointer");	
	try { 
		dsOnText = ( (e.explicitOriginalTarget.nodeType==document.TEXT_NODE && !dsTextDoesntCount.test(e.target) && 
							!(pointercur && dsBlacklist.linksBLon)) || dsCountsAsText.test(e.target));
	} catch(err) { dsOnText = false; }
	
	// save the selected text for later copying to clipboard if necessary
	if (dsInQT) {
		dsDownStr = e.originalTarget.ownerDocument.defaultView.getSelection().toString();
		// if it's time to leave texttoggle, do it
		if (e.button==dsButton && !dsOnText && dsQToffCnt==dsQTonDrag) {
			dsStrToCpy = dsDownStr;
			dsTextToggle(false);
		}
	}
}

// catches clicks for quick toggle
// preempt the normal image size toggling to allow dragging of images
// preempt clicks triggered by drags, clicks meant to stop momentum
function dsClickPreempt(e) 
{ 
	// QT logic
	if (dsInQT) {
		// not a real click-- bail out
		if (dsSavedDown != null) {
			if ((Math.abs(dsSavedDown.sx-e.screenX) > dsshortdX) || (Math.abs(dsSavedDown.sy-e.screenY) > dsshortdX)) {
				return true;
			}
		}
		// a click for exiting QT...
		if (e.button==dsButton && !dsOnText) {	
			// save for later copying to clipboard..
			if (e.detail==1 && dsCopyOnQToff) {
				dsStrToCpy = dsDownStr; // save for 2nd click if necessary
			}
			// if we triggered exiting QT...
			if (e.detail>=dsQToffCnt) dsTextToggle(false);
		}
		return true;
	} 
	
	// everything below called only when G&D is on and not in QT:
	
	// start quick toggle from clicking, etc. on text node
	if (e.button==dsButton && e.detail>=dsQTonCnt && dsQTonCnt>=dsQTonDrag &&
								dsSavedDown!=null && !dsOnItem(e.originalTarget) && dsOnText) {	
		dsTextToggle(true);
		return true;
	}
	// preempt image toggling
	if (e.originalTarget.ownerDocument instanceof HTMLDocument) {
		if (!(dsSavedDown) && (typeof e.originalTarget.ownerDocument.toggleImageSize == 'function') && 
					e.originalTarget.nodeName.toLowerCase()=="img" && e.button==dsButton && e.button==dsLeft) {					 
			e.preventDefault(); e.stopPropagation(); // stop propagation to keep clicks from reaching the browser(?) and triggering image rescaling
			dsWasScrolling=false; 
			return false;
		}
	}
	// preempt if click was to stop momentum/flick scrolling, and "fake" clicks generated 
	// while dragging. this must be handled at the appcontent level in order to work, but we 
	// only want to preempt WasScrolling clicks if the scrolling really was ended (so user 
	// can still click other appcontent UI elements during scrolling)
	if ((dsWasScrolling && (dsScrollIntervalObj==null)) || !(dsSavedDown)) { 
		e.preventDefault(); e.stopPropagation(); 
		dsWasScrolling=false; 
		return false;
	}
}

function dsOnItem(initialNode) 
{
	var nextNode, currNode;
	var doc = initialNode.ownerDocument;
	var st = doc.defaultView.getComputedStyle(initialNode, "");
	var cur = st.getPropertyValue("cursor").replace(/"|'/g,"");

	// Never preempt XUL objects or other non-HTML stuff (counts as "items")
	if (initialNode.namespaceURI == "http://www.mozilla.org/keymaster/gatekeeper/there.is.only.xul") return true;
	if (!(doc instanceof HTMLDocument)) return true; // e.g. xml documents

	// If it's on the blacklist, it's an "item"	
	if (dsBlacklist.test(initialNode)) return true;
	
	// documents in design mode are editable so they count as "items" to avoid conflicts with basic editing clicks, etc
	if (doc.designMode) if (doc.designMode=="on") return true;  

	// Anything styled with cursors that imply draggability is counted as an "item";
	// Anything styled with link-style "pointer" cursor is treated like a link
	if ([dsStdCursor,dsDragCursor,"auto","default"].indexOf(cur)==-1) {
		if (/move|grab|resize/i.test(cur)) return true;
		if (/pointer/i.test(cur) && dsBlacklist.linksBLon) return true; 
	}
	
	// Strict mode logic: also consider to be an "item" anything...
	// - styled with a weird mouse cursor - trying to disable click/drag element selection - editable via moz-user-modify
	if (dsStrict) {
		if ([dsStdCursor,dsDragCursor,"auto","default"].indexOf(cur)==-1) {
			return true;	
		}
		if (st.getPropertyValue("-moz-user-select")=="none") {
			return true; //was a hack for Google maps...
		}
		if (doc.defaultView.getComputedStyle(initialNode, "").getPropertyValue("-moz-user-modify") != "read-only") {
			if (dsButton==dsLeft) return true;
		}
	}

	return false;
}

function dsDownHandler(e) 
{
	// Special cases to bail out on unless the click was to stop previous scrolling: 
	//  - clicked a different button - on an item - in quick-toggle mode
	// (yes, we let any mouse button count to stop the scrolling, for user convenience)
	if (!dsWasScrolling && (e.button!=dsButton || dsInQT || dsOnItem(dsSavedDown.target))) {
		return true; 
	}

	// If there is previous scrolling from momentum/flick, stop it before proceeding 
	if (dsScrollIntervalObj != null) {
		window.clearInterval(dsScrollIntervalObj); 
		dsScrollIntervalObj = null;

		// Special bail out case: clicked on the scrollbar or other UI elements not part of page
		if (dsSavedDown.target.namespaceURI == "http://www.mozilla.org/keymaster/gatekeeper/there.is.only.xul") {
			return true;
		}
		
		e.stopPropagation();
	}	

	// prevent default mouse down actions
	e.preventDefault();
		
	// record start data for scrolling/gestures before adding listeners, just in case of a race
	dsStartY = e.screenY; dsStartX = e.screenX; dsMoveTime=0;
	dsDragDoc = dsSavedDown.target.ownerDocument;

	// Figure out what we will be scrolling (if nothing scrollable found, bail out!)
	dsScrollObj = dsFindNodeToScroll(dsSavedDown.target);
	if (!dsScrollObj.nodeToScrollX && !dsScrollObj.nodeToScrollY) {
		return false;
	}

	// Remove pre-drag listeners, etc, replace with active dragging versions
	dsRenderingArea.removeEventListener("mousedown", dsDownHandler, true);
	dsAppContent.removeEventListener("mousedown",dsDownPreempt, true);
	if (dsCIbrowser) {
		dsCIbrowser.removeEventListener("mousedown", dsDownHandler, true);
		dsCIbox.removeEventListener("mousedown",dsDownPreempt, true);
	}
	window.addEventListener("mouseup", dsUpHandler, true);
	window.addEventListener("mousemove", dsMoveScrollBar, true);
	window.addEventListener("mousedown", dsUpHandler, true);

	// Finish up initializations
	dsLastY = e.screenY; dsLastX = e.screenX;
	dsLastMoveX = e.screenX; dsLastMoveY = e.screenY;
	dsLastVel = 0;
	dsLastTime=(new Date()).getTime(); 
	clearDragInfo();
	
	// Set dragging cursor 
	if (dsStdCursor!=dsDragCursor) {
		if (dsDragDoc instanceof HTMLDocument) dsSetCursor(dsDragDoc, dsDragCursor, false);
	}
}

function dsMoveScrollBar(e) 
{
	var horiz, time, dX, dY, dXM, dYM, dT, dD, vel;

	e.preventDefault(); e.stopPropagation();   
	window.clearTimeout(dsTO); 
	time = (new Date()).getTime();
	dT = time-dsLastTime; 
	dX = dsLastX - e.screenX;  dY = dsLastY - e.screenY; // how far mouse cursor moved since last function call
	horiz = (Math.abs(dX) > Math.abs(dY));
	
	// ignore slight quick movements 
	if ((dsSavedDown) && dT<=dsshortdT && 
				Math.abs(dsStartX-e.screenX)<=dsshortdX && Math.abs(dsStartY-e.screenY)<=dsshortdX) {
		return;
	}
	
	// text toggle triggered from horiz dragging on text w/o clicking
	if (dsSavedDown!=null && horiz && dsOnText && dsQTonCnt==dsQTonDrag && !dsOnItem(dsSavedDown.target)) {		
		window.removeEventListener("mousemove", dsMoveScrollBar, true);
		window.removeEventListener("mouseup", dsUpHandler, true);
		window.removeEventListener("mousedown", dsUpHandler, true);
		window.removeEventListener("DOMContentLoaded", dsUpHandler, true);		
		domWindowUtils.sendMouseEventToWindow(dsSavedDown.type,dsSavedDown.x,dsSavedDown.y,dsSavedDown.button,dsSavedDown.count,dsSavedDown.modifier);
		dsRenderingArea.addEventListener("mousedown", dsDownHandler, true);
		dsAppContent.addEventListener("mousedown",dsDownPreempt, true);
		if (dsCIbrowser) {
			dsCIbrowser.addEventListener("mousedown", dsDownHandler, true);
			dsCIbox.addEventListener("mousedown",dsDownPreempt, true);
		}
		dsTextToggle(true);
		return;	
	}
	
	// If we're moving for the first time, null out dsSavedDown (this is how we check whether we moved or not later)
	if ((dsSavedDown) && (Math.abs(dsStartX-e.screenX) > dsshortdX || Math.abs(dsStartY-e.screenY) > dsshortdX)) {
		dsSavedDown = null;
		dsMoveTime = time;
	}

	// record the _effective_ screen scroll movement for gesture analysis (even if we don't actually scroll for this call)
	if (dsFlickOn||dsMomOn) {
		if (horiz) dD = dX*dsScrollObj.ratioX; else dD = dY*dsScrollObj.ratioY;
		if (dT==0) return;
		vel = dD/dT;   
		// changed principle scroll direction-- reset data
		if ((dsScrollHoriz!=horiz) || (dD*dsLastVel<0)) {  
			clearDragInfo();
		}
		dsDists.add(dD); dsVels.add(vel); dsTimes.add(dT);
		dsLastVel = vel;
	}
	
	dsScrollHoriz = horiz; 
	dsLastTime = time; dsLastY = e.screenY; dsLastX = e.screenX; 

	// dsLastMoveX/Y are floating point measures in mouse cursor space that keep track of the decimal remainder pixels left over after scrolling. 
	// This is important for precision when scroll ratios are not 1, in particular for full page zoom mode
	dXM = (dsLastMoveX - e.screenX)*dsScrollObj.ratioX;
	dYM = (dsLastMoveY - e.screenY)*dsScrollObj.ratioY;
	
	// Scroll the appropriate amount
	if ((Math.abs(dXM)>=dsDragInc) || (Math.abs(dYM)>=dsDragInc)) {
		dsLastMoveX = e.screenX + (dXM - Math.round(dXM))/dsScrollObj.ratioX;
		dsLastMoveY = e.screenY + (dYM - Math.round(dYM))/dsScrollObj.ratioY;
		if (horiz && dsScrollObj.nodeToScrollX) dsScrollObj.scrollXBy(Math.round(dXM));
		if (dsScrollObj.nodeToScrollY) dsScrollObj.scrollYBy(Math.round(dYM));
	}
	
	// if user doesn't move for a while, reset gesture analysis data
	dsTO=window.setTimeout(function() { clearDragInfo(); }, Math.max(2*dT,200)); 
}

function clearDragInfo() { dsDists.clear(); dsVels.clear(); dsTimes.clear(); };

function dsBigDecel() 
{	
	var N = dsTimes.sumWithin(dsMomExtent); 
	var M = dsVels.maxabs(0,N);
	return (dsVels.maxabs(0,1)/M < dsMomVariation);
}

function dsUpHandler(e) 
{  
	// get rid of the dragging listeners, etc
	window.clearTimeout(dsTO); 
	window.removeEventListener("mousemove", dsMoveScrollBar, true);
	window.removeEventListener("mouseup", dsUpHandler, true);
	window.removeEventListener("mousedown", dsUpHandler, true);
	window.removeEventListener("DOMContentLoaded", dsUpHandler, true);

	var time = (new Date()).getTime(); 
	var dT = time-dsLastTime;
	var aT = dsTimes.biasedAvg(1,50);
	
	// handle flick gestures and momentum
	var scrollStarted=false;
	if ( (dT<2*aT) && (dsFlickOn||dsMomOn) ) {	// first cond to review
		var dist, vel, interval, DXt, DYt, totCurDist;
		DXt = e.screenX - dsStartX; DYt = e.screenY - dsStartY;
		DXt*=dsScrollObj.ratioX; DYt*=dsScrollObj.ratioY; 
		
		totCurDist = Math.abs(dsDists.sum()/(dsScrollHoriz?dsScrollObj.ratioX:dsScrollObj.ratioY));
		interval=7; // 200fps
		dsScrollMaxInterval = aT*3;
		if (dsFlickOn && (time-dsMoveTime < dsFlickTimeLimit)) {  
			// FLICK
			vel = sgn(dsVels.val(0))*dsFlickSpeed;
			// Previous page or next page
			if (dsScrollHoriz && vel<0 && (dsFlickHoriz==2 || 
						(dsFlickHoriz==1 && (!dsScrollObj.nodeToScrollX || dsScrollObj.scrollLeft==0)))) {
				BrowserBack();
			} else if (dsScrollHoriz && vel>0 && dsFlickHoriz==3) {
				BrowserBack();
			} else if (dsScrollHoriz && vel>0 && (dsFlickHoriz==2 ||
						(dsFlickHoriz==1 && (!dsScrollObj.nodeToScrollX || dsScrollObj.scrollLeft==dsScrollObj.scrollW-dsScrollObj.realWidth)))) {
				BrowserForward();				
			} else if (dsScrollHoriz && vel<0 && dsFlickHoriz==3) {
				BrowserForward();
			} else {
				if (dsFlickWholePage) {
					if (dsScrollHoriz) dist = sgn(vel)*(dsScrollObj.scrollW);
					else dist = sgn(vel)*(dsScrollObj.scrollH);
				} else {
					if (dsScrollHoriz) dist = sgn(vel)*(dsScrollObj.realWidth - 15*dsScrollObj.ratioX - Math.abs(DXt));
					else dist = sgn(vel)*(dsScrollObj.realHeight - 15*dsScrollObj.ratioY - Math.abs(DYt));
				}
				dsInitScroll(dist,interval,vel,dsScrollHoriz,false);
				scrollStarted=true;
			}
		} else if (dsMomOn) {
			// MOMENTUM
			if (!dsBigDecel() && (totCurDist > 3) && 
						(dsTimes.sum() > dsMomExtent/4) && (dsDists.length>1)) {		// 2nd cond to review
				vel = sgn(dsVels.val(0))*dsVels.maxabs(0,1);
				if (dsScrollHoriz) dist = sgn(vel)*(dsScrollObj.scrollW);
				else dist = sgn(vel)*(dsScrollObj.scrollH);
				dsInitScroll(dist,interval,vel,dsScrollHoriz,true);
				scrollStarted=true;
			}
		}
	} // flick/momentum handlers (if triggered, scrollStarted = true now)
	
	// prevent right-click menu and middle-button autoscroll.
	if (e.button != dsLeft) e.preventDefault(); // scrollbar bug fixed if we don't preventdefault here for primary button.. is this ok?

	var t = e.originalTarget;
	
	// go back to standard pre-drag cursor 
	if (dsStdCursor!=dsDragCursor) {
		if (dsDragDoc instanceof HTMLDocument) dsSetCursor(dsDragDoc, dsStdCursor,false);
	}
	
	// put back the standard pre-drag listeners, etc
	dsRenderingArea.addEventListener("mousedown", dsDownHandler, true);
	dsAppContent.addEventListener("mousedown",dsDownPreempt, true);
	if (dsCIbrowser) {
		dsCIbrowser.addEventListener("mousedown", dsDownHandler, true);
		dsCIbox.addEventListener("mousedown",dsDownPreempt, true);
	}
	
	//  if we did scroll, but are done (no flick/momentum), give kb focus to the scrolled element
	if (!(dsSavedDown) && !scrollStarted) {
		//var focused = document.commandDispatcher.focusedElement;
		//if (focused) focused.blur();
		if (dsScrollObj.clientFrame instanceof Window) {
			dsScrollObj.clientFrame.focus();
			// focus the div for kb input, unless it will kill a selection.
			var sel = dsScrollObj.clientFrame.getSelection();
			if (!sel || sel.isCollapsed) {	// not sure why but sometimes getSelection() returns null
				if ((dsScrollObj.nodeToScrollX instanceof Element) && dsScrollHoriz) {
					dsScrollObj.nodeToScrollX.focus(); 			
					//focused = document.commandDispatcher.focusedElement;
					//if (focused) focused.blur();
				}
				else if (dsScrollObj.nodeToScrollY instanceof Element) {
					dsScrollObj.nodeToScrollY.focus();
					//focused = document.commandDispatcher.focusedElement;
					//if (focused) focused.blur();
				}
			}
		}  	
	}
}

// helper to make clicks etc focus scrollable elts for keyboard input and to be default window for text selection etc
function dsFixFocus(n) 
{
	//var focused = document.commandDispatcher.focusedElement;
	//if (focused) focused.blur();
	
	n.ownerDocument.defaultView.focus();
	n.ownerDocument.documentElement.focus();
	if (dsScrollObj.clientFrame instanceof Window) dsScrollObj.clientFrame.focus();
	if (dsScrollObj.deepestNode) {
		dsScrollObj.deepestNode.focus();
		//document.commandDispatcher.focusedElement.blur();
	}
	
	//focused = document.commandDispatcher.focusedElement;
	//if (focused) focused.blur();

}

// handle some useful default browser click actions that we prevented with preventDefault 
// in the mousedown handler.
function dsClickHandler(e) 
{
	// wrong button-- bail out
	if (e.button != dsButton) return; 
	
	var t = e.originalTarget, br = gBrowser.getBrowserForDocument(e.target.ownerDocument);
	  
	// re-enable middle button autoscrolling (uses same checks as browser.xml)
	try { 
		if (e.button==dsMiddle && dsPrefRoot.getBoolPref("general.autoScroll") && !br.isAutoscrollBlocker(t) && 
					!br._scrollingView && br.currentURI.spec!="about:blank") {
			br.startScroll(e);
		}
	} catch(e) {}
	
	// re-enable right-click context menu for non-Windows platforms -- code modified from Marc Boullet's Scrollbar Anywhere
	if (dsPlatform!=dsWindows && dsButton==dsRight) {		
		with (t.ownerDocument.defaultView) {
			if (!nsContextMenu.prototype._setTargetInternal) {
				nsContextMenu.prototype._setTargetInternal = nsContextMenu.prototype.setTarget;
				nsContextMenu.prototype.setTarget = function(aNode, aRangeParent, aRangeOffset) {
					this._setTargetInternal(aNode, aRangeParent, this._rangeOffset);
				};
			}
			nsContextMenu.prototype._rangeOffset = e.rangeOffset;
		}
		dsSetClearContextListener(false);
		var evt = t.ownerDocument.createEvent("MouseEvents");
		evt.initMouseEvent("contextmenu", true, true, t.defaultView, 0,	e.screenX, e.screenY, e.clientX, e.clientY, false, false, false, false, 2, null);
		t.dispatchEvent(evt);		
		dsSetClearContextListener(true);
	}

	if (dsOnItem(t) || dsInQT) return; 
	
	// handle left-click focus/deselection actions if they were prevented before
	if (e.button==dsLeft) {
	 	dsFixFocus(t);
 		try { t.ownerDocument.defaultView.goDoCommand("cmd_selectNone"); } catch(err) { }
	}
}

function dsToggleKeyHandler(e) 
{
	// "safety feature" to not allow hotkey thats just a regular key 
	if (!dsUseCtrl && !dsUseAlt && !dsUseShift && dsTogKey < 112) return;
	
	if (e.keyCode==dsTogKey && e.ctrlKey==dsUseCtrl && e.altKey==dsUseAlt && e.shiftKey==dsUseShift) {
		dsToggle();
	}
}


function dsSetCursor(doc, cur, deep) 
{
	if (!doc) return;
	if (doc instanceof HTMLDocument) {
		if (doc.designMode) if (doc.designMode=="on") cur="auto"; // don't change cursor in design mode docs
		if (dsBlacklist.test(doc.body)) cur="auto";
		if (doc.documentElement.style.cursor != cur) {
			doc.documentElement.style.setProperty("cursor", cur, "important");
		}
	}
	if (deep && (doc.evaluate)) {
		var i;		
		var x = doc.evaluate("//frame | //iframe", doc, null, XPathResult.UNORDERED_NODE_SNAPSHOT_TYPE,null);
		if (x) {
			for (i=0; i<x.snapshotLength; i++) {
				dsSetCursor(x.snapshotItem(i).contentDocument,cur,deep);
			}
		}
	}
}

// called when new webpage loads
function dsLoad(e) {
	dsUpdateBrowser(e.target);
}

function dsUpdateBrowser(doc) {
	dsUpdateButton();	
	if (!doc) doc=content.document;
	
	var BL=dsBlacklist.test(doc.documentElement);
	dsSetCursor(doc, ((dsOn&&!dsInQT&&!BL)?dsStdCursor:"auto"),true);	
	if (gBrowser.getBrowserForDocument(doc)) {
		gBrowser.getBrowserForDocument(doc).setAttribute("autoscroll",(!dsOn || dsInQT || BL || dsButton != 1));
	} 
	
	if (dsCIbrowser) {	
		doc = dsCIbrowser.contentDocument;	
		BL=dsBlacklist.test(doc.documentElement);
		dsSetCursor(doc, ((dsOn&&!dsInQT&&!BL)?dsStdCursor:"auto"),true);	
		dsCIbrowser.setAttribute("autoscroll",(!dsOn || dsInQT || BL || dsButton != 1));
	}
}

function dsUpdateButton() {
	var bu = document.getElementById("dragscroll-button");
	if (bu) {
		if (dsOn && dsBlacklist.test(content.document.documentElement)) {
			bu.setAttribute("dsOn","BL");
		} else if (dsInQT) {
			bu.setAttribute("dsOn","QT");
		} else {
			bu.setAttribute("dsOn",dsOn);
		}
	}
}

function dsTextToggle(QTon) {
	if (QTon == null) {
		dsInQT=!dsInQT;	
		dsUpdateBrowser();
	} else if (QTon != dsInQT) {
		dsInQT = QTon;	
		dsUpdateBrowser();		
	}
	if (dsCopyOnQToff && dsInQT==false && (dsStrToCpy)) {
		try { 
			dsClipboardHelper.copyString(dsStrToCpy); 
			window.goDoCommand("cmd_selectNone");	
		} catch(err) { }		
	}
	dsStrToCpy = null;
}
function dsToggle() {
	if (dsInQT) dsTextToggle(false);
	else dsPref.setBoolPref("on", !dsOn);
}

function dsInitScroll(dist,interval,vel,horiz,friction)
{
	if (horiz && !dsScrollObj.nodeToScrollX) return;
	if (!horiz && !dsScrollObj.nodeToScrollY) return;
	dsScrollLastLoop = (new Date()).getTime();
	
	if (dsScrollIntervalObj != null) window.clearInterval(dsScrollIntervalObj); 
	var destination;
	dsSmoothFactor=2;
	if (horiz) {
		destination = dsScrollObj.scrollLeft + dist;
		if (destination <= 0) { 
			dist = -dsScrollObj.scrollLeft; 
			dsSmoothFactor=3; 
		} else if (destination >= dsScrollObj.scrollW-dsScrollObj.realWidth)  {
			dist = dsScrollObj.scrollW-dsScrollObj.realWidth-dsScrollObj.scrollLeft;
			dsSmoothFactor=3; 
		}
	} else {
		destination = dsScrollObj.scrollTop + dist;
		if (destination <= 0) {
			dist = -dsScrollObj.scrollTop;
			dsSmoothFactor=3; 
		} else if (destination >= dsScrollObj.scrollH-dsScrollObj.realHeight)  {
			dist = dsScrollObj.scrollH-dsScrollObj.realHeight-dsScrollObj.scrollTop;
			dsSmoothFactor=3; 
		}
	}
	dsScrollLoopInterval = interval;
	dsScrollVel = vel;
	dsScrollVelMult = 1;
	dsScrollHoriz = horiz;
	dsScrollToGo = Math.round(dist);	// can be fractional thanks to zoom levels..
	dsScrollFrictionMult = (friction?1-dsMomFriction:1);
	dsScrollLastMoveLoop = dsScrollLastLoop;
	dsScrollIntervalObj = window.setInterval(dsScrollLoop,dsScrollLoopInterval); 
	dsScrollLoop();
}

function dsScrollLoop() 
{
	var toScroll, currentTime, dT, tCk;
	currentTime=(new Date()).getTime();
	// make sure previous loop is done(?)
	if (dsScrollLastLoop==currentTime) {
		window.clearInterval(dsScrollIntervalObj);
		dsScrollIntervalObj = window.setInterval(function() { dsScrollLoop(); },dsScrollLoopInterval);
		return;
	}
	dsScrollLastLoop = currentTime;
	dT = currentTime-dsScrollLastMoveLoop;

	// the following line sacrifices constant speed for smoother motion when the loop is delayed a lot
	if (currentTime-dsScrollLastLoop>dsScrollMaxInterval) dT=dsScrollMaxInterval;
	
	dsScrollVel *= dsScrollFrictionMult;
	toScroll = Math.round(dsScrollVel*dsScrollVelMult*dT);	
	// with friction, we end the loop as soon as we aren't moving in a time step. Must check this before the next 
	// statement to avoid infinite loop
	if (toScroll==0 && dsScrollFrictionMult<1) { 
		window.clearInterval(dsScrollIntervalObj);
		dsScrollIntervalObj=null;
		return;
	}
	// if there's still distance to go and we're moving slowly enough to not scroll a pixel this time, loop
	if (Math.abs(toScroll)<dsDragInc*dsScrollVelMult && Math.abs(dsScrollToGo)>=dsDragInc*dsScrollVelMult) return;
	 // the following must be before smooth velocity scaling below or loop may not end
	if (toScroll==0 && dsScrollToGo!=0) return;
	if ((dsScrollToGo-toScroll)*sgn(dsScrollToGo) <= 0) {
		toScroll=dsScrollToGo;
	}	
	// fast (tho somewhat inaccurate) hack to smoothly stop
	tCk = Math.max(30,dT)*dsSmoothFactor*dsScrollVel;
	while (dsSmoothStop && ((dsScrollToGo-tCk*dsScrollVelMult)*sgn(dsScrollToGo) < 0)) {
		// it's important that we take ceil below so the last pixel always finishes
		toScroll=sgn(toScroll)*Math.ceil(Math.abs(toScroll)/2);  
		dsScrollVelMult*=0.3;
	}
	dsScrollLastMoveLoop = dsScrollLastLoop;

	if (dsScrollHoriz) dsScrollObj.scrollXBy(toScroll);
	else dsScrollObj.scrollYBy(toScroll);
	dsScrollToGo -= toScroll;

	if (dsScrollToGo==0){
		window.clearInterval(dsScrollIntervalObj);
		dsScrollIntervalObj=null;
		return;
	}
}

function convertPrefs() 
{	
	var i, err, pre;
	var bools  = ["on", "useCtrl", "useAlt", "useShift", "sbmode", "samecur", "reverse", 
					"flickon", "momOn", "smoothStop", "qtOffCopy", "qtOn", "strict"]; 
	var ints = ["togKey", "button", "qtOnCnt", "qtOffCnt", "flickwhole", "flickhoriz"];
	var chars = ["grabCursor","grabbingCursor", "mult", "dragInc", "flickspeed_ppms", 
					"flicktimelimit", "momExtent", "momVariation", "momFriction"];
  				
	for (i=0; i<bools.length; i++) {
		try { 
			dsPrefRoot.setBoolPref("extensions.dragscroll." + bools[i],dsPrefRoot.getBoolPref("dragscroll." + bools[i]));
		} catch(err) { }
	}
	for (i=0; i<ints.length; i++) {
		try { 
			dsPrefRoot.setIntPref("extensions.dragscroll." + ints[i],dsPrefRoot.getIntPref("dragscroll." + ints[i]));
		} catch(err) { }
  	}
	for (i=0; i<chars.length; i++) {
		try { 
			dsPrefRoot.setCharPref("extensions.dragscroll." + chars[i],dsPrefRoot.getCharPref("dragscroll." + chars[i]));
		} catch(err) { }
	}

	var bl = JSON.parse(dsPrefRoot.getCharPref("extensions.dragscroll.hiddenBL"+String(dsPrefRoot.getIntPref("extensions.dragscroll.button"))));
	var linkdisable = true;
	for (i=0; i<bl.length; i++) {    
		if (bl[i].url=="*" && bl[i].elem=='*:link,*:visited,*[role="link"]') {
			linkdisable = (bl[i].on=="true");
			break;
		}
	}
	dsPrefRoot.clearUserPref("extensions.dragscroll.hiddenBL0");
	dsPrefRoot.clearUserPref("extensions.dragscroll.hiddenBL1");
	dsPrefRoot.clearUserPref("extensions.dragscroll.hiddenBL2");

	try { pre = dsPrefRoot.getIntPref("dragscroll.preLevel"); } catch(err) { pre = 1; }
	if (pre==0) {	// no grabbing on text --> hover texttoggle
		dsPrefRoot.setBoolPref("extensions.dragscroll.qtOn",true);
		dsPrefRoot.setIntPref("extensions.dragscroll.qtOnCnt",-1);
		dsPrefRoot.setIntPref("extensions.dragscroll.qtOffCnt",-1);
	}
	if ((pre==2) || !linkdisable) {	// grabbing on links
		bl = JSON.parse(dsPrefRoot.getCharPref("extensions.dragscroll.hiddenBL"+String(dsPrefRoot.getIntPref("extensions.dragscroll.button"))));
		for (i=0; i<bl.length; i++) {
			if (bl[i].id=="links") {
				bl[i].on = false;
				break;
			}
		}
		dsPrefRoot.setCharPref("extensions.dragscroll.hiddenBL"+String(dsPrefRoot.getIntPref("extensions.dragscroll.button")),JSON.stringify(bl));
	}
}

function updateHiddenBLs()
{
	var oldBL, newBL, button, i, j;
	for (button=0; button<3; button++) {
		oldBL = JSON.parse(dsPrefRoot.getCharPref("extensions.dragscroll.hiddenBL" + String(button)));
		dsPrefRoot.clearUserPref("extensions.dragscroll.hiddenBL" + String(button));
		newBL = JSON.parse(dsPrefRoot.getCharPref("extensions.dragscroll.hiddenBL" + String(button)));
		for (i=0; i<newBL.length; i++) {
			for (j=0; j<oldBL.length; j++) {
				if (oldBL[j].id == newBL[i].id) {
					newBL[i].on = oldBL[j].on;
					break;
				}	
			}	
		}
		dsPrefRoot.setCharPref("extensions.dragscroll.hiddenBL" + String(button),JSON.stringify(newBL));
	}		
}


// The following is modified from Marc Boullet's All-in-one Gestures extension
function dsFindNodeToScroll(initialNode) 
{
	
	function getStyle(elem, aProp) {
		var p = elem.ownerDocument.defaultView.getComputedStyle(elem, "").getPropertyValue(aProp);
		var val = parseFloat(p);
		if (!isNaN(val)) return Math.ceil(val);
		if (p == "thin") return 1;
		if (p == "medium") return 3;
		if (p == "thick") return 5;
		return 0;
	}

	function scrollCursorType(neededW, availW, neededH, availH, scrollBarSize) {
		if (neededW <= availW && neededH <= availH) return 3;
		if (neededW > availW && neededH > availH) return 0;
		if (neededW > availW) return ((neededH <= (availH - scrollBarSize)) - 0) << 1;  // 0 or 2
		return (neededW <= (availW - scrollBarSize)) - 0;
	}
  
	const defaultScrollBarSize = 16;
	const twiceScrollBarSize = defaultScrollBarSize * 2;
	var retObj = {isXML: false, nodeToScrollX: null, nodeToScrollY: null, deepestNode: null,
								ratioX: 1, ratioY: 1, clientFrame: null, isFrame: false,
								targetDoc: null, insertionNode: null, realHeight: 1, realWidth: 1, 
								scrollXBy: null, scrollYBy: null, scrollW: 1, scrollH: 1 };
	var realWidth, realHeight, nextNode, currNode, scrollType;
	var targetDoc = initialNode.ownerDocument;
	var docEl = targetDoc.documentElement;
	retObj.insertionNode = (docEl) ? docEl : targetDoc;
	var docBox = docEl.getBoundingClientRect(retObj.insertionNode);
	var clientFrame = targetDoc.defaultView;
	retObj.targetDoc = targetDoc; retObj.clientFrame = clientFrame;
	if (targetDoc instanceof HTMLDocument) { // walk the tree up looking for something to scroll
		if (clientFrame.frameElement) retObj.isFrame = true; else retObj.isFrame = false;
		var bodies = docEl.getElementsByTagName("body");
		if (!bodies || !bodies.length) 
			return retObj;
		var bodyEl = bodies[0];
		if (initialNode == docEl) nextNode = bodyEl;
		else if (initialNode.nodeName.toLowerCase() == "select") nextNode = initialNode.parentNode;
		else nextNode = initialNode;
		do {
			try {
				currNode = nextNode;
				scrollType = 3;
				if (currNode instanceof Element && currNode.ownerDocument.defaultView.getComputedStyle(currNode, "").getPropertyValue("overflow") != "hidden") {
					realWidth = currNode.clientWidth + getStyle(currNode, "border-left-width") + getStyle(currNode, "border-right-width");
					realHeight = currNode.clientHeight + getStyle(currNode, "border-top-width") + getStyle(currNode, "border-bottom-width");

					// note: we ignore DIVs etc with "visible" overflow but allow it for body and html elements, 
					// which get scrollbars automatically in frames or from the browser.
					if (["html","body"].indexOf(currNode.nodeName.toLowerCase())>-1 ||
						currNode.ownerDocument.defaultView.getComputedStyle(currNode, "").getPropertyValue("overflow") != "visible") {
						// if the newer, more reliable API is available, use it. 
						if (currNode.scrollTopMax!==undefined && currNode.scrollLeftMax!==undefined) {
							// leave a margin to ignore divs with tiny 1-2px scroll areas from (apparently?) rounding errors, etc
							if (currNode.scrollTopMax>2 && currNode.scrollLeftMax>2) scrollType = 0;
							if (currNode.scrollTopMax>2 && currNode.scrollLeftMax<=2) scrollType = 1;
							if (currNode.scrollTopMax<=2 && currNode.scrollLeftMax>2) scrollType = 2;					
						} else {
							scrollType = scrollCursorType(currNode.scrollWidth, realWidth, currNode.scrollHeight, realHeight, 0);
						}
					}
				}
				if (scrollType != 3) {
					if (!retObj.deepestNode) retObj.deepestNode = currNode;
					if ((scrollType==0 || scrollType==2) && (!retObj.nodeToScrollX)) {
						retObj.nodeToScrollX = currNode;
						if (realWidth > twiceScrollBarSize) realWidth -= twiceScrollBarSize;
						if (dsSBMode) retObj.ratioX = -currNode.scrollWidth/realWidth; 
						else retObj.ratioX = dsMult;
						retObj.ratioX *= dsReverse;
						retObj.ratioX /= gBrowser.selectedBrowser.markupDocumentViewer.fullZoom; // "full zoom" unaccounted for in node scrolling code
						retObj.scrollW = currNode.scrollWidth-twiceScrollBarSize; 
						retObj.realWidth = realWidth;
						retObj.scrollXBy = function(dx) { if (this.nodeToScrollX instanceof Element) this.nodeToScrollX.scrollLeft += dx; }
						retObj.__defineGetter__("scrollLeft",function(){ return (this.nodeToScrollX instanceof Element)?this.nodeToScrollX.scrollLeft:0;});
					}
					if ((scrollType==0 || scrollType==1) && (!retObj.nodeToScrollY)) {
						retObj.nodeToScrollY = currNode;
						if (realHeight > twiceScrollBarSize) realHeight -= twiceScrollBarSize;
						if (dsSBMode) retObj.ratioY = -currNode.scrollHeight/realHeight;
						else retObj.ratioY = dsMult;
						retObj.ratioY *= dsReverse;
						retObj.ratioY /= gBrowser.selectedBrowser.markupDocumentViewer.fullZoom; // "full zoom" unaccounted for in node scrolling code
						retObj.scrollH = currNode.scrollHeight-twiceScrollBarSize;
						retObj.realHeight = realHeight;
						retObj.scrollYBy = function(dy) { if (this.nodeToScrollY instanceof Element) { this.nodeToScrollY.scrollTop += dy; } }
						retObj.__defineGetter__("scrollTop",function(){return (this.nodeToScrollY instanceof Element)?this.nodeToScrollY.scrollTop:0;});
					}
					if (retObj.nodeToScrollX && retObj.nodeToScrollY)	
						return retObj;
				}
				nextNode = currNode.parentNode;
			}
			catch(err) {
				return retObj;
			}
		} while (nextNode && currNode != docEl);
		if (retObj.isFrame) {
			if (retObj.nodeToScrollX || retObj.nodeToScrollY) {
				return retObj;
			} else {
				return dsFindNodeToScroll(clientFrame.frameElement.ownerDocument.documentElement);
			}
		}
	}
	else { // XML document; do our best
		retObj.nodeToScrollX = initialNode;
		retObj.nodeToScrollY = initialNode;
		retObj.deepestNode = initialNode;
		if (docBox) {
			if (dsSBMode) {
				retObj.ratioX = -docBox.width/dsRenderingArea.boxObject.width;
				retObj.ratioY = -docBox.height/dsRenderingArea.boxObject.height;
			} else {
				retObj.ratioX = dsMult;
				retObj.ratioY = dsMult;
			}	            	
			retObj.ratioX *= dsReverse;
			retObj.ratioY *= dsReverse;
			retObj.ratioX /= gBrowser.selectedBrowser.markupDocumentViewer.fullZoom; // "full zoom" unaccounted for in node scrolling code
			retObj.ratioY /= gBrowser.selectedBrowser.markupDocumentViewer.fullZoom; // "full zoom" unaccounted for in node scrolling code
			retObj.scrollW = docBox.width;
			retObj.scrollH = docBox.height;
			retObj.realWidth = dsRenderingArea.boxObject.width;
			retObj.realHeight = dsRenderingArea.boxObject.height;
			try { scrollType = scrollCursorType(docBox.width, dsRenderingArea.boxObject.width,
								docBox.height, dsRenderingArea.boxObject.height, defaultScrollBarSize); } catch(err) { }
			if (scrollType==0 || scrollType==2)	retObj.nodeToScrollX = initialNode;
			if (scrollType==0 || scrollType==1)	retObj.nodeToScrollY = initialNode;
		}
		retObj.isXML = true;
		retObj.scrollXBy = function(dx) { this.clientFrame.scrollBy(dx,0); }
		retObj.scrollYBy = function(dy) { this.clientFrame.scrollBy(0,dy); }
		retObj.__defineGetter__("scrollTop",function(){return this.clientFrame.scrollY;});
		retObj.__defineGetter__("scrollLeft",function(){return this.clientFrame.scrollX;});
	}
	return retObj;
}
// End AiOG


}	// end dragscrollExtensionNS

var dsScrollIntervalObj=null;
var dragscrollExtension = new dragscrollExtensionNS();
window.addEventListener("load", dragscrollExtension.dsInit, false);
window.addEventListener("keydown", dragscrollExtension.dsToggleKeyHandler, false); 
window.addEventListener("unload", dragscrollExtension.dsClose, false);

