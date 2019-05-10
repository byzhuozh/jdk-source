/*
 * Copyright (c) 1996, 2007, Oracle and/or its affiliates. All rights reserved.
 * ORACLE PROPRIETARY/CONFIDENTIAL. Use is subject to license terms.
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 */

package sun.awt.windows;

import sun.awt.PlatformFont;

public class WFontPeer extends PlatformFont {

    private String textComponentFontName;

    public WFontPeer(String name, int style){
        super(name, style);
        if (fontConfig != null) {
            textComponentFontName = ((WFontConfiguration) fontConfig).getTextComponentFontName(familyName, style);
        }
    }

    protected char getMissingGlyphCharacter() {
        return '\u2751';
    }

    static {
        /* NB Headless printing uses AWT Fonts */
        initIDs();
    }

    /**
     * Initialize JNI field and method IDs
     */
    private static native void initIDs();
}
