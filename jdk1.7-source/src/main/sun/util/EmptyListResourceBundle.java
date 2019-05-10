/*
 * Copyright (c) 2005, 2007, Oracle and/or its affiliates. All rights reserved.
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

package sun.util;

import java.util.ListResourceBundle;

public class EmptyListResourceBundle extends ListResourceBundle {
    @Override
    protected final Object[][] getContents() {
        return new Object[][] {};
    }
}
