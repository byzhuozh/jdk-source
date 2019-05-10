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

import sun.nio.cs.ext.MS1256;

/**
 * A table to convert Cp1256 to Unicode
 *
 * @author  ConverterGenerator tool
 */

public class ByteToCharCp1256 extends ByteToCharSingleByte {

    private final static MS1256 nioCoder = new MS1256();

    public String getCharacterEncoding() {
        return "Cp1256";
    }

    public ByteToCharCp1256() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}
