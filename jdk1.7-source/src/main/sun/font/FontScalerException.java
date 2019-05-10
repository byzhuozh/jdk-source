/*
 * Copyright (c) 2007, Oracle and/or its affiliates. All rights reserved.
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

package sun.font;

public class FontScalerException extends Exception {
    public FontScalerException() {
      super("Font scaler encountered runtime problem.");
    }

    public FontScalerException(String reason) {
      super (reason);
    }
}
