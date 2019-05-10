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

import sun.nio.cs.MS1253;

/**
 * A table to convert Cp1253 to Unicode
 *
 * @author  ConverterGenerator tool
 */

public class ByteToCharCp1253 extends ByteToCharSingleByte {

    private final static MS1253 nioCoder = new MS1253();

    public String getCharacterEncoding() {
        return "Cp1253";
    }

    public ByteToCharCp1253() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}
