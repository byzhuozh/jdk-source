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

import sun.nio.cs.ext.IBM500;

/**
 * A table to convert to Cp500 to Unicode
 *
 * @author  ConverterGenerator tool
 */

public class ByteToCharCp500 extends ByteToCharSingleByte {

    private final static IBM500 nioCoder = new IBM500();

    public String getCharacterEncoding() {
        return "Cp500";
    }

    public ByteToCharCp500() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}
