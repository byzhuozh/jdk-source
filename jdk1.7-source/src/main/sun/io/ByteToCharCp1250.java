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

import sun.nio.cs.MS1250;

/**
 * A table to convert Cp1250 to Unicode
 *
 * @author  ConverterGenerator tool
 */

public class ByteToCharCp1250 extends ByteToCharSingleByte {

    private final static MS1250 nioCoder = new MS1250();

    public String getCharacterEncoding() {
        return "Cp1250";
    }

    public ByteToCharCp1250() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}
