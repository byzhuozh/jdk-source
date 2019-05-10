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

import sun.nio.cs.ext.IBM861;

/**
 * A table to convert to Cp861 to Unicode
 *
 * @author  ConverterGenerator tool
 */

public class ByteToCharCp861 extends ByteToCharSingleByte {

    private final static IBM861 nioCoder = new IBM861();

    public String getCharacterEncoding() {
        return "Cp861";
    }

    public ByteToCharCp861() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}
