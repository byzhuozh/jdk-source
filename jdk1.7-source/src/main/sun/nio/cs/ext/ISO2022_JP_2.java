/*
 * Copyright (c) 2005, Oracle and/or its affiliates. All rights reserved.
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

package sun.nio.cs.ext;

import java.nio.charset.Charset;

public class ISO2022_JP_2 extends ISO2022_JP
{
    public ISO2022_JP_2() {
        super("ISO-2022-JP-2",
              ExtendedCharsets.aliasesFor("ISO-2022-JP-2"));
    }

    public String historicalName() {
        return "ISO2022JP2";
    }

    public boolean contains(Charset cs) {
      return super.contains(cs) ||
             (cs instanceof JIS_X_0212) ||
             (cs instanceof ISO2022_JP_2);
    }

    protected DoubleByteDecoder get0212Decoder() {
        return new JIS_X_0212_Decoder(this);
    }

    protected DoubleByteEncoder get0212Encoder() {
        return new JIS_X_0212_Encoder(this);
    }

}
