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

import sun.nio.cs.IBM852;

/**
 * A table to convert to Cp852 to Unicode
 *
 * @author  ConverterGenerator tool
 */

public class ByteToCharCp852 extends ByteToCharSingleByte {

    private final static IBM852 nioCoder = new IBM852();

    public String getCharacterEncoding() {
        return "Cp852";
    }

    public ByteToCharCp852() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}
