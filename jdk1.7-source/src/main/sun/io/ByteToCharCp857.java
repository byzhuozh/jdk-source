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

import sun.nio.cs.IBM857;

/**
 * A table to convert to Cp857 to Unicode
 *
 * @author  ConverterGenerator tool
 */

public class ByteToCharCp857 extends ByteToCharSingleByte {

    private final static IBM857 nioCoder = new IBM857();

    public String getCharacterEncoding() {
        return "Cp857";
    }

    public ByteToCharCp857() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}
