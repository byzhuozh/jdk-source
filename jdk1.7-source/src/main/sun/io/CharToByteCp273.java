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

import sun.nio.cs.ext.IBM273;

/**
 * Tables and data to convert Unicode to Cp273
 *
 * @author  ConverterGenerator tool
 */

public class CharToByteCp273 extends CharToByteSingleByte {

    private final static IBM273 nioCoder = new IBM273();

    public String getCharacterEncoding() {
        return "Cp273";
    }

    public CharToByteCp273() {
        super.mask1 = 0xFF00;
        super.mask2 = 0x00FF;
        super.shift = 8;
        super.index1 = nioCoder.getEncoderIndex1();
        super.index2 = nioCoder.getEncoderIndex2();
    }
}
