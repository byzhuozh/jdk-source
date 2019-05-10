/*
 * Copyright (c) 2002, 2003, Oracle and/or its affiliates. All rights reserved.
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

import sun.nio.cs.ext.IBM1047;

/**
 * A table to convert to Cp1047 to Unicode
 *
 * @author  ConverterGenerator tool
 */

public class ByteToCharCp1047 extends ByteToCharSingleByte {

    private final static IBM1047 nioCoder = new IBM1047();

    public String getCharacterEncoding() {
        return "Cp1047";
    }

    public ByteToCharCp1047() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}
