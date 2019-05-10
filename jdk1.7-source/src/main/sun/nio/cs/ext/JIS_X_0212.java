/*
 * Copyright (c) 2002, 2003, Oracle and/or its affiliates. All rights reserved.
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

/*
 */

package sun.nio.cs.ext;

import java.nio.charset.Charset;
import java.nio.charset.CharsetDecoder;
import java.nio.charset.CharsetEncoder;

public class JIS_X_0212
    extends Charset
{

    public JIS_X_0212() {
        super("JIS_X0212-1990", ExtendedCharsets.aliasesFor("JIS_X0212-1990"));
    }

    public boolean contains(Charset cs) {
        return (cs instanceof JIS_X_0212);
    }

    public CharsetDecoder newDecoder() {
        return new Decoder(this);
    }

    public CharsetEncoder newEncoder() {
        return new JIS_X_0212_Encoder(this);
    }

    private static class Decoder extends JIS_X_0212_Decoder {
        protected char decodeSingle(int b) {
            return DoubleByteDecoder.REPLACE_CHAR;
        }

        public Decoder(Charset cs) {
            super(cs);
        }
    }
}
