/*
 * Copyright (c) 1999, Oracle and/or its affiliates. All rights reserved.
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
 * Convert arrays containing Unicode characters into arrays of bytes, using
 * big-endian byte order and writing an initial byte-order mark.
 */

public class CharToByteUTF16 extends CharToByteUnicode {

    public CharToByteUTF16() {
        super(BIG, true);
    }

    public String getCharacterEncoding() {
        return "UTF-16";
    }

}
