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

import sun.nio.cs.ext.TIS_620;

/**
 * A table to convert TIS620 to Unicode
 *
 * @author  ConverterGenerator tool
 */

public class ByteToCharTIS620 extends ByteToCharSingleByte {

    private final static TIS_620 nioCoder = new TIS_620();

    public String getCharacterEncoding() {
        return "TIS620";
    }

    public ByteToCharTIS620() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}
