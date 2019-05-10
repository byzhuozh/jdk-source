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

import sun.nio.cs.MS1250;

/**
 * Tables and data to convert Unicode to Cp1250
 *
 * @author  ConverterGenerator tool
 */

public class CharToByteCp1250 extends CharToByteSingleByte {

    private final static MS1250 nioCoder = new MS1250();

    public String getCharacterEncoding() {
        return "Cp1250";
    }

    public CharToByteCp1250() {
        super.mask1 = 0xFF00;
        super.mask2 = 0x00FF;
        super.shift = 8;
        super.index1 = nioCoder.getEncoderIndex1();
        super.index2 = nioCoder.getEncoderIndex2();
    }
}
