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

import sun.nio.cs.ext.IBM1098;

/**
 * A table to convert to Cp1098 to Unicode
 *
 * @author  ConverterGenerator tool
 */

public class ByteToCharCp1098 extends ByteToCharSingleByte {

    private final static IBM1098 nioCoder = new IBM1098();

    public String getCharacterEncoding() {
        return "Cp1098";
    }

    public ByteToCharCp1098() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}
