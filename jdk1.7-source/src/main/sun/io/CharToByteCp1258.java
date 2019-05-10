/*
 * Copyright (c) 1996, 2003, Oracle and/or its affiliates. All rights reserved.
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

import sun.nio.cs.ext.MS1258;

/**
 * Tables and data to convert Unicode to Cp1258
 *
 * @author  ConverterGenerator tool
 */

public class CharToByteCp1258 extends CharToByteSingleByte {

    private final static MS1258 nioCoder = new MS1258();

    public String getCharacterEncoding() {
        return "Cp1258";
    }

    public CharToByteCp1258() {
        super.mask1 = 0xFF00;
        super.mask2 = 0x00FF;
        super.shift = 8;
        super.index1 = nioCoder.getEncoderIndex1();
        super.index2 = nioCoder.getEncoderIndex2();
    }
}
