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

import sun.nio.cs.ext.IBM424;

/**
 * A table to convert to Cp424 to Unicode
 *
 * @author  ConverterGenerator tool
 */

public class ByteToCharCp424 extends ByteToCharSingleByte {

    private final static IBM424 nioCoder = new IBM424();

    public String getCharacterEncoding() {
        return "Cp424";
    }

    public ByteToCharCp424() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}
