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

import sun.nio.cs.ext.IBM273;

/**
 * A table to convert to Cp273 to Unicode
 *
 * @author  ConverterGenerator tool
 */

public class ByteToCharCp273 extends ByteToCharSingleByte {

    private final static IBM273 nioCoder = new IBM273();

    public String getCharacterEncoding() {
        return "Cp273";
    }

    public ByteToCharCp273() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}
