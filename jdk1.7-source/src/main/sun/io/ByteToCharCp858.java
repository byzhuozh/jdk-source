/*
 * Copyright (c) 1998, Oracle and/or its affiliates. All rights reserved.
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

package sun.io;

/**
 * A table to convert Cp858 to Unicode.  This converter differs from
 * Cp850 is one code point, 0xD5, which changes from \u0131 to \u20AC.
 * @author  Alan Liu
 */
public class ByteToCharCp858 extends ByteToCharCp850 {
    public ByteToCharCp858() {}

    public String getCharacterEncoding() {
        return "Cp858";
    }

    protected char getUnicode(int byteIndex) {
        // Change single code point with respect to parent.
        // Cast to byte to get sign extension to match byteIndex.
        return (byteIndex == (byte)0xD5) ? '\u20AC' : super.getUnicode(byteIndex);
    }
}

//eof
