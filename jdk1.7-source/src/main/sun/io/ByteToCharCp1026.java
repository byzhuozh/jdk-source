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

import sun.nio.cs.ext.IBM1026;

/**
 * A table to convert to Cp1026 to Unicode
 *
 * @author  ConverterGenerator tool
 */

public class ByteToCharCp1026 extends ByteToCharSingleByte {

    private final static IBM1026 nioCoder = new IBM1026();

    public String getCharacterEncoding() {
        return "Cp1026";
    }

    public ByteToCharCp1026() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}
