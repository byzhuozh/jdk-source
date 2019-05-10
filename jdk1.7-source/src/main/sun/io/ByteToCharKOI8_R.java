/*
 * Copyright (c) 1997, 2003, Oracle and/or its affiliates. All rights reserved.
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

import sun.nio.cs.KOI8_R;

/**
 * A table to convert KOI8_R to Unicode
 *
 * @author  ConverterGenerator tool
 */

public class ByteToCharKOI8_R extends ByteToCharSingleByte {

    private final static KOI8_R nioCoder = new KOI8_R();

    public String getCharacterEncoding() {
        return "KOI8_R";
    }

    public ByteToCharKOI8_R() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}
