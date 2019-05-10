/*
 * Copyright (c) 1997, 2003, Oracle and/or its affiliates. All rights reserved.
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

import sun.nio.cs.ext.MS874;

/**
 * Tables and data to convert Unicode to MS874
 *
 * @author  ConverterGenerator tool
 */

public class CharToByteMS874 extends CharToByteSingleByte {

    private final static MS874 nioCoder = new MS874();

    public String getCharacterEncoding() {
        return "MS874";
    }

    public CharToByteMS874() {
        super.mask1 = 0xFF00;
        super.mask2 = 0x00FF;
        super.shift = 8;
        super.index1 = nioCoder.getEncoderIndex1();
        super.index2 = nioCoder.getEncoderIndex2();
    }
}
