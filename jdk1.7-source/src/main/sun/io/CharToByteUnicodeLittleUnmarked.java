/*
 * Copyright (c) 1996, 1999, Oracle and/or its affiliates. All rights reserved.
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
 * little-endian byte order; do not write a byte-order mark before the first
 * converted character.
 *
 * @author      Mark Reinhold
 */

public class CharToByteUnicodeLittleUnmarked extends CharToByteUnicode {

    public CharToByteUnicodeLittleUnmarked () {
        byteOrder = LITTLE;
        usesMark = false;
    }

}
