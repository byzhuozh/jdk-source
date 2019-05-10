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

import sun.nio.cs.ext.MacRomania;

/**
 * A table to convert to MacRomania to Unicode
 *
 * @author  ConverterGenerator tool
 */

public class ByteToCharMacRomania extends ByteToCharSingleByte {

    private final static MacRomania nioCoder = new MacRomania();

    public String getCharacterEncoding() {
        return "MacRomania";
    }

    public ByteToCharMacRomania() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}
