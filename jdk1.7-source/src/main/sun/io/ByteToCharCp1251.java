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

import sun.nio.cs.MS1251;

/**
 * A table to convert Cp1251 to Unicode
 *
 * @author  ConverterGenerator tool
 */

public class ByteToCharCp1251 extends ByteToCharSingleByte {

    private final static MS1251 nioCoder = new MS1251();

    public String getCharacterEncoding() {
        return "Cp1251";
    }

    public ByteToCharCp1251() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}
