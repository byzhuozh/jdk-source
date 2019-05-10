/*
 * Copyright (c) 1998, 2010, Oracle and/or its affiliates. All rights reserved.
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

package sun.tools.native2ascii.resources;

import java.util.ListResourceBundle;

public class MsgNative2ascii_zh_CN extends ListResourceBundle {

    public Object[][] getContents() {
        Object[][] temp = new Object[][] {
        {"err.bad.arg", "-encoding \u9700\u8981\u53C2\u6570"},
        {"err.cannot.read",  "\u65E0\u6CD5\u8BFB\u53D6{0}\u3002"},
        {"err.cannot.write", "\u65E0\u6CD5\u5199\u5165{0}\u3002"},
        {"usage", "\u7528\u6CD5: native2ascii [-reverse] [-encoding encoding] [inputfile [outputfile]]"},
        };

        return temp;
    }
}
