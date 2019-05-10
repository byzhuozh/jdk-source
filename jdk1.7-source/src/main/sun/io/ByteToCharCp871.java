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

import sun.nio.cs.ext.IBM871;

/**
 * A table to convert to Cp871 to Unicode
 *
 * @author  ConverterGenerator tool
 */

public class ByteToCharCp871 extends ByteToCharSingleByte {

    private final static IBM871 nioCoder = new IBM871();

    public String getCharacterEncoding() {
        return "Cp871";
    }

    public ByteToCharCp871() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}
