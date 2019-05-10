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

import sun.nio.cs.ext.MacSymbol;

/**
 * A table to convert to MacSymbol to Unicode
 *
 * @author  ConverterGenerator tool
 */

public class ByteToCharMacSymbol extends ByteToCharSingleByte {

    private final static MacSymbol nioCoder = new MacSymbol();

    public String getCharacterEncoding() {
        return "MacSymbol";
    }

    public ByteToCharMacSymbol() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}
