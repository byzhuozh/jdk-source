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

import sun.nio.cs.ext.IBM037;

/**
 * A table to convert to Cp037 to Unicode
 *
 * @author  ConverterGenerator tool
 */

public class ByteToCharCp037 extends ByteToCharSingleByte {

    private final static IBM037 nioCoder = new IBM037();

    public String getCharacterEncoding() {
        return "Cp037";
    }

    public ByteToCharCp037() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}
