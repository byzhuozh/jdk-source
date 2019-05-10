/*
 * Copyright (c) 1996, Oracle and/or its affiliates. All rights reserved.
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
 * little-endian byte order.
 *
 * @author      Mark Reinhold
 */

public class CharToByteUnicodeLittle extends CharToByteUnicode {

    public CharToByteUnicodeLittle () {
        byteOrder = LITTLE;
    }

}
