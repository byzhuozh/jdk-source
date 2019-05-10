/*
 * Copyright (c) 2006, Oracle and/or its affiliates. All rights reserved.
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

import sun.nio.cs.ext.*;

public class ByteToCharCp834 extends ByteToCharDBCS_ASCII {

    public String getCharacterEncoding() {
        return "Cp834";
    }

    public ByteToCharCp834() {
        super((DoubleByte.Decoder)new IBM834().newDecoder());
    }
}
