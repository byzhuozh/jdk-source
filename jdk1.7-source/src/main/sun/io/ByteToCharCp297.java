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

import sun.nio.cs.ext.IBM297;

/**
 * A table to convert to Cp297 to Unicode
 *
 * @author  ConverterGenerator tool
 */

public class ByteToCharCp297 extends ByteToCharSingleByte {

    private final static IBM297 nioCoder = new IBM297();

    public String getCharacterEncoding() {
        return "Cp297";
    }

    public ByteToCharCp297() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}
