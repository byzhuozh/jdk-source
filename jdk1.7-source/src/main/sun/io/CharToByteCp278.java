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

import sun.nio.cs.ext.IBM278;

/**
 * Tables and data to convert Unicode to Cp278
 *
 * @author  ConverterGenerator tool
 */

public class CharToByteCp278 extends CharToByteSingleByte {

    private final static IBM278 nioCoder = new IBM278();

    public String getCharacterEncoding() {
        return "Cp278";
    }

    public CharToByteCp278() {
        super.mask1 = 0xFF00;
        super.mask2 = 0x00FF;
        super.shift = 8;
        super.index1 = nioCoder.getEncoderIndex1();
        super.index2 = nioCoder.getEncoderIndex2();
    }
}
