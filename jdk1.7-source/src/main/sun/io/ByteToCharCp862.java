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

import sun.nio.cs.IBM862;

/**
 * A table to convert to Cp862 to Unicode
 *
 * @author  ConverterGenerator tool
 */

public class ByteToCharCp862 extends ByteToCharSingleByte {

    private final static IBM862 nioCoder = new IBM862();

    public String getCharacterEncoding() {
        return "Cp862";
    }

    public ByteToCharCp862() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}
