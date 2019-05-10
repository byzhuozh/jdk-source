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

import sun.nio.cs.ext.IBM838;

/**
 * Tables and data to convert Unicode to Cp838
 *
 * @author  ConverterGenerator tool
 */

public class CharToByteCp838 extends CharToByteSingleByte {

    private final static IBM838 nioCoder = new IBM838();

    public String getCharacterEncoding() {
        return "Cp838";
    }

    public CharToByteCp838() {
        super.mask1 = 0xFF00;
        super.mask2 = 0x00FF;
        super.shift = 8;
        super.index1 = nioCoder.getEncoderIndex1();
        super.index2 = nioCoder.getEncoderIndex2();
    }
}
