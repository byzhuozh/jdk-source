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

import java.nio.charset.*;
import sun.awt.AWTCharset;

public class WDefaultFontCharset extends AWTCharset
{
    static {
       initIDs();
    }

    // Name for Windows FontSet.
    private String fontName;

    public WDefaultFontCharset(String name){
        super("WDefaultFontCharset", Charset.forName("windows-1252"));
        fontName = name;
    }

    public CharsetEncoder newEncoder() {
        return new Encoder();
    }

    private class Encoder extends AWTCharset.Encoder {
        public boolean canEncode(char c){
            return canConvert(c);
        }
    }

    public synchronized native boolean canConvert(char ch);

    /**
     * Initialize JNI field and method IDs
     */
    private static native void initIDs();
}
