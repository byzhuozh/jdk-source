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
 * A table to convert Cp1145 to Unicode.  This converter differs from
 * Cp284 is one code point, 0x9F, which changes from \u00A4 to \u20AC.
 * @author  Alan Liu
 */
public class ByteToCharCp1145 extends ByteToCharCp284 {
    public ByteToCharCp1145() {}

    public String getCharacterEncoding() {
        return "Cp1145";
    }

    protected char getUnicode(int byteIndex) {
        // Change single code point with respect to parent.
        // Cast to byte to get sign extension to match byteIndex.
        return (byteIndex == (byte)0x9F) ? '\u20AC' : super.getUnicode(byteIndex);
    }
}

//eof
