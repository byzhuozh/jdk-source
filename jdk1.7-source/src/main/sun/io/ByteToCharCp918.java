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

import sun.nio.cs.ext.IBM918;

/**
 * A table to convert to Cp918 to Unicode
 *
 * @author  ConverterGenerator tool
 */

public class ByteToCharCp918 extends ByteToCharSingleByte {

    private final static IBM918 nioCoder = new IBM918();

    public String getCharacterEncoding() {
        return "Cp918";
    }

    public ByteToCharCp918() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}
