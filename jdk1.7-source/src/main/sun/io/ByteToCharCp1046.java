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

import sun.nio.cs.ext.IBM1046;

/**
 * A table to convert to Cp1046 to Unicode
 *
 * @author  ConverterGenerator tool
 */

public class ByteToCharCp1046 extends ByteToCharSingleByte {

    private final static IBM1046 nioCoder = new IBM1046();

    public String getCharacterEncoding() {
        return "Cp1046";
    }

    public ByteToCharCp1046() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}
