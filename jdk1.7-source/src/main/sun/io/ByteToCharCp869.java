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

import sun.nio.cs.ext.IBM869;

/**
 * A table to convert to Cp869 to Unicode
 *
 * @author  ConverterGenerator tool
 */

public class ByteToCharCp869 extends ByteToCharSingleByte {

    private final static IBM869 nioCoder = new IBM869();

    public String getCharacterEncoding() {
        return "Cp869";
    }

    public ByteToCharCp869() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}
