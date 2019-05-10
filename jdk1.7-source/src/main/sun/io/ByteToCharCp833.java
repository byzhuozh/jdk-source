/*
 * Copyright (c) 2010, Oracle and/or its affiliates. All rights reserved.
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

import sun.nio.cs.ext.IBM833;

public class ByteToCharCp833 extends ByteToCharSingleByte {

    private final static IBM833 nioCoder = new IBM833();

    public String getCharacterEncoding() {
        return "Cp833";
    }

    public ByteToCharCp833() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}

