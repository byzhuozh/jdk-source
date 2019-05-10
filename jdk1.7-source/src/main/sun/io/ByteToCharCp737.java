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

import sun.nio.cs.IBM737;

/**
 * A table to convert to Cp737 to Unicode
 *
 * @author  ConverterGenerator tool
 */

public class ByteToCharCp737 extends ByteToCharSingleByte {

    private final static IBM737 nioCoder = new IBM737();

    public String getCharacterEncoding() {
        return "Cp737";
    }

    public ByteToCharCp737() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}
