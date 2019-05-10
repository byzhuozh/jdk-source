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

import sun.nio.cs.ext.IBM1097;

/**
 * A table to convert to Cp1097 to Unicode
 *
 * @author  ConverterGenerator tool
 */

public class ByteToCharCp1097 extends ByteToCharSingleByte {

    private final static IBM1097 nioCoder = new IBM1097();

    public String getCharacterEncoding() {
        return "Cp1097";
    }

    public ByteToCharCp1097() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}
