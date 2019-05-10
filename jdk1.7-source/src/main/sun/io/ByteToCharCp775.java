/*
 * Copyright (c) 1996, 2005, Oracle and/or its affiliates. All rights reserved.
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

import sun.nio.cs.IBM775;

/**
 * A table to convert to Cp775 to Unicode
 *
 * @author  ConverterGenerator tool
 */

public class ByteToCharCp775 extends ByteToCharSingleByte {

    private final static IBM775 nioCoder = new IBM775();

    public String getCharacterEncoding() {
        return "Cp775";
    }

    public ByteToCharCp775() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}
