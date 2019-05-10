/*
 * Copyright (c) 1996, Oracle and/or its affiliates. All rights reserved.
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

package sun.tools.jar;

import java.io.IOException;

public
class JarException extends IOException {
    public JarException() {
        super();
    }

    public JarException(String s) {
        super(s);
    }
}
