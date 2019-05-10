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

/*
 * (C) Copyright Taligent, Inc. 1996, 1997 - All Rights Reserved
 * (C) Copyright IBM Corp. 1996 - 1999 - All Rights Reserved
 *
 * The original version of this source code and documentation
 * is copyrighted and owned by Taligent, Inc., a wholly-owned
 * subsidiary of IBM. These materials are provided under terms
 * of a License Agreement between Taligent and Sun. This technology
 * is protected by multiple US and International patents.
 *
 * This notice and attribution to Taligent may not be removed.
 * Taligent is a registered trademark of Taligent, Inc.
 *
 */

package sun.text.resources;

import java.util.ListResourceBundle;

public class FormatData_zh_TW extends ListResourceBundle {
    /**
     * Overrides ListResourceBundle
     */
    protected final Object[][] getContents() {
        return new Object[][] {
            { "Eras",
                new String[] { // era strings
                    "\u897f\u5143\u524d",
                    "\u897f\u5143"
                }
            },
            { "NumberPatterns",
                new String[] {
                    "#,##0.###;-#,##0.###", // decimal pattern
                    "\u00A4#,##0.00;-\u00A4#,##0.00", // currency pattern
                    "#,##0%" // percent pattern
                }
            },
            { "DateTimePatterns",
                new String[] {
                    "ahh'\u6642'mm'\u5206'ss'\u79d2' z", // full time pattern
                    "ahh'\u6642'mm'\u5206'ss'\u79d2'", // long time pattern
                    "a hh:mm:ss", // medium time pattern
                    "a h:mm", // short time pattern
                    "yyyy'\u5e74'M'\u6708'd'\u65e5' EEEE", // full date pattern
                    "yyyy'\u5e74'M'\u6708'd'\u65e5'", // long date pattern
                    "yyyy/M/d", // medium date pattern
                    "yyyy/M/d", // short date pattern
                    "{1} {0}" // date-time pattern
                }
            },
            { "DateTimePatternChars", "GyMdkHmsSEDFwWahKzZ" },
        };
    }
}
