/*
 * Copyright (c) 1996, 2005, Oracle and/or its affiliates. All rights reserved.
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

import sun.nio.cs.IBM874;

/**
 * Tables and data to convert Unicode to Cp874
 *
 * @author  ConverterGenerator tool
 */

public class CharToByteCp874 extends CharToByteSingleByte {

    private final static IBM874 nioCoder = new IBM874();

    public String getCharacterEncoding() {
        return "Cp874";
    }

    public CharToByteCp874() {
        super.mask1 = 0xFF00;
        super.mask2 = 0x00FF;
        super.shift = 8;
        super.index1 = nioCoder.getEncoderIndex1();
        super.index2 = nioCoder.getEncoderIndex2();
    }
}
