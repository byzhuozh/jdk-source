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

import sun.nio.cs.ext.IBM922;

/**
 * Tables and data to convert Unicode to Cp922
 *
 * @author  ConverterGenerator tool
 */

public class CharToByteCp922 extends CharToByteSingleByte {

    private final static IBM922 nioCoder = new IBM922();

    public String getCharacterEncoding() {
        return "Cp922";
    }

    public CharToByteCp922() {
        super.mask1 = 0xFF00;
        super.mask2 = 0x00FF;
        super.shift = 8;
        super.index1 = nioCoder.getEncoderIndex1();
        super.index2 = nioCoder.getEncoderIndex2();
    }
}
