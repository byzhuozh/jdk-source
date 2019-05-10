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

import sun.nio.cs.ext.IBM860;

/**
 * Tables and data to convert Unicode to Cp860
 *
 * @author  ConverterGenerator tool
 */

public class CharToByteCp860 extends CharToByteSingleByte {

    private final static IBM860 nioCoder = new IBM860();

    public String getCharacterEncoding() {
        return "Cp860";
    }

    public CharToByteCp860() {
        super.mask1 = 0xFF00;
        super.mask2 = 0x00FF;
        super.shift = 8;
        super.index1 = nioCoder.getEncoderIndex1();
        super.index2 = nioCoder.getEncoderIndex2();
    }
}
