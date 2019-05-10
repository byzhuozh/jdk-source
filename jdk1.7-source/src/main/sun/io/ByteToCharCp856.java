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

import sun.nio.cs.ext.IBM856;

/**
 * A table to convert to Cp856 to Unicode
 *
 * @author  ConverterGenerator tool
 */

public class ByteToCharCp856 extends ByteToCharSingleByte {

    private final static IBM856 nioCoder = new IBM856();

    public String getCharacterEncoding() {
        return "Cp856";
    }

    public ByteToCharCp856() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}
