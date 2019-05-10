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

import sun.nio.cs.IBM866;

/**
 * Tables and data to convert Unicode to Cp866
 *
 * @author  ConverterGenerator tool
 */

public class CharToByteCp866 extends CharToByteSingleByte {

    private final static IBM866 nioCoder = new IBM866();

    public String getCharacterEncoding() {
        return "Cp866";
    }

    public CharToByteCp866() {
        super.mask1 = 0xFF00;
        super.mask2 = 0x00FF;
        super.shift = 8;
        super.index1 = nioCoder.getEncoderIndex1();
        super.index2 = nioCoder.getEncoderIndex2();
    }
}
