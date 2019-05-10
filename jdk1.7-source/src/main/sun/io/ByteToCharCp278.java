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

import sun.nio.cs.ext.IBM278;

/**
 * A table to convert to Cp278 to Unicode
 *
 * @author  ConverterGenerator tool
 */

public class ByteToCharCp278 extends ByteToCharSingleByte {

    private final static IBM278 nioCoder = new IBM278();

    public String getCharacterEncoding() {
        return "Cp278";
    }

    public ByteToCharCp278() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}
