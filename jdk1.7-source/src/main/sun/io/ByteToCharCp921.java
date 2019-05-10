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

import sun.nio.cs.ext.IBM921;

/**
 * A table to convert to Cp921 to Unicode
 *
 * @author  ConverterGenerator tool
 */

public class ByteToCharCp921 extends ByteToCharSingleByte {

    private final static IBM921 nioCoder = new IBM921();

    public String getCharacterEncoding() {
        return "Cp921";
    }

    public ByteToCharCp921() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}
