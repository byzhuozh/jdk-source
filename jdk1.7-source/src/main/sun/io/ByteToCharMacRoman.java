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

import sun.nio.cs.ext.MacRoman;

/**
 * A table to convert to MacRoman to Unicode
 *
 * @author  ConverterGenerator tool
 */

public class ByteToCharMacRoman extends ByteToCharSingleByte {

    private final static MacRoman nioCoder = new MacRoman();

    public String getCharacterEncoding() {
        return "MacRoman";
    }

    public ByteToCharMacRoman() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}
