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

import sun.nio.cs.MS1252;

/**
 * Tables and data to convert Unicode to Cp1252
 *
 * @author  ConverterGenerator tool
 */

public class CharToByteCp1252 extends CharToByteSingleByte {

    private final static MS1252 nioCoder = new MS1252();

    public String getCharacterEncoding() {
        return "Cp1252";
    }

    public CharToByteCp1252() {
        super.mask1 = 0xFF00;
        super.mask2 = 0x00FF;
        super.shift = 8;
        super.index1 = nioCoder.getEncoderIndex1();
        super.index2 = nioCoder.getEncoderIndex2();
    }
}
