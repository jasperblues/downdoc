'use strict'

const { execSync } = require('node:child_process')
const fs = require('node:fs')
const path = require('node:path')

const DIAGRAM_STYLES = { graphviz: true, dot: true }
const LANGUAGE_MAP = { gradle: 'groovy', jinja: 'html', django: 'html' }

const ADMONS = JSON.parse(
  '{"CAUTION":"\ud83d\udd25","IMPORTANT":"\u2757","NOTE":"\ud83d\udccc","TIP":"\ud83d\udca1","WARNING":"\u26a0\ufe0f"}'
)
const ATTRIBUTES = JSON.parse(
  '{"empty":"","idprefix":"_","idseparator":"_","markdown-line-break":"\\\\","markdown-strikethrough":"~~",' +
    '"nbsp":"&#160;","quotes":"<q> </q>","sp":" ","vbar":"|","zwsp":"&#8203;"}'
)
const BREAKS = { "'''": '---', '***': '---', '---': '---', '<<<': undefined, 'toc::[]': undefined }
const CONUMS = [...Array(19)].reduce((obj, _, i) => (obj[i + 1] = String.fromCharCode(0x2460 + i)) && obj, {})
const DELIMS = { '----': 'v', '....': 'v', '====': 'c', '|===': 't', '--': 'c', '****': 'c', ____: 'c', '++++': 'p' }
const DELIM_CHARS = new Set(['-', '.', '=', '*', '_', '+'])
const LIST_MARKERS = [1, 2, 3, 4, 5, 6, 7, 8, 9, '*', '.', '<', '-'].reduce((obj, c) => (obj['' + c] = true) && obj, {})
const NORMAL_SUBS = ['quotes', 'attributes', 'macros']
const SUBSTITUTORS = { quotes, attributes, macros, callouts }
const TDIV = { '': '| --- ', '<': '| :-- ', '^': '| :-: ', '>': '| --: ' }
const AttributeEntryRx = /^:(!)?([^:-][^:]*):(?:$| (.+))/
const AttributeRefRx = /(\\)?\{([\p{Ll}\d_][\p{Ll}\d_-]*)\}/gu
const AuthorInfoLineRx = /^(?:[\p{Alpha}\d_]+(?: +[\p{Alpha}\d_]+){0,2}(?: +<([^>]+)>)?(?:; |$))+$/u
const BlockAnchorRx = /^\[([\p{L}_][\p{Alpha}\d_\-:.]*)(?:, ?(.+))?\]$/u
const BlockImageMacroRx = /^image::([^\s[][^[]*)\[(.*)\]$/
const CellDelimiterRx = /(?:(?:^| +)(?:[<>^.]*[a-z]?)|)\| */
const ConumRx = /(^| )<([.1-9]|1\d)>(?=(?: <(?:[.1-9]|1\d)>)*$)/g
const DlistItemRx = /^(?!\/\/)(\S.*?)(:{2,4})(?: (.+))?($)/
const ElementAttributeRx = /(?:^|, *)(?:(\w[\w-]*)=)?(?:("|')([^\2]+?)\2|([^,]+|))/g
const EmphasisSpanMetaRx = /(?<![\p{L}\d_\\])\[[^[\]]+\](?=_(?:\S|\S.*?\S)_(?![\p{L}\d_]))/gu
const InlineAnchorRx = /\[\[([\p{L}_][\p{Alpha}\d_\-:.]*)\]\]/u
const InlineImageMacroRx = /image:([^\s:`[\\][^[\\]*)\[(|.*?[^\\])\]/g
const InlineStemMacroRx = /stem:\[(.*?[^\\])\]/g
const LinkMacroRx = /(\\)?(?:(?:link:(?!:)|(https?:\/\/))([^\s[\\]+)(\[(|.*?[^\\])\^?\])|(https?:\/\/)([^\s[\]]+))/g
const ListItemRx = /^(\*+|\.+|<(?:[.1-9]|1\d)>|-|\d+\.) +(.+)/
const MarkedSpanRx = /(?<![\p{L}\d_\\])(?:\[((\.line-through)|[^[\]]+)\])?#(\S|\S.*?\S)#(?![\p{L}\d_])/gu
const PreprocessorDirectiveRx = /^\\?(?:(if)(n)?def|include)::([^[]+)\[(.+)?\]$/
const QuotedSpanRx = /("|')`(\S|\S.*?\S)`\1/g
const RevisionInfoLineRx = /^v(\d+(?:[-.]\w+)*)(?:, (\d+-\d+-\d+))?|(\d+-\d+-\d+)$/
const RewriteInternalXrefRx = /\[([^[]*?)\]\(#!([^)]+)\)/g
const StrongSpanRx = /(?<![\p{L}\d_\\])(?:\[[^[\]]+\])?(\*(?:\S|\S.*?\S)\*)(?![\p{L}\d_])/gu
const StyleShorthandMarkersRx = /([.#%])/
const XrefMacroRx = /(\\)?xref:(?![\s:`])(?:([^#[\\]+)(#[^\s[\\]*|\.adoc)|#([^\s[\\]+)|([^#[\\]+))\[(|.*?[^\\])\]/g
const XrefShorthandRx = /<<([^\s,>][^,>]*)(?:, ?([^>]+))?>>/g

module.exports = function downdoc (asciidoc, {
  attributes: initialAttrs = {},
  basePath,
  includedPaths = new Set(),
} = {}) {
  basePath = basePath || (typeof process !== 'undefined' && process.cwd ? process.cwd() : '.')
  const attrs = new Map(Object.entries(Object.assign({}, ATTRIBUTES, initialAttrs)))
  const lines = asciidoc.split(attrs.delete('doctitle') ? '\n' : '\n')
  if (lines[lines.length - 1] === '') lines.pop()
  let inContainer, inHeader, inList, inPara, inTable, indent
  inHeader = (inContainer = inPara = (indent = '') || false) || asciidoc[0] === '=' || !!~asciidoc.indexOf('\n= ')
  let blockAttrs, blockTitle, chr0, grab, hardbreakNext, listStack, match, next, subs, style, verbatim
  const [containerStack, nrefs, refs, skipStack, undef] = [(listStack = []).slice(), new Map(), new Map(), [], () => {}]
  return lines
    .reduce((accum, line, idx) => {
      while ((grab = match = next = style = subs = undefined) === undefined) {
        if (skipStack.length && (match = skipStack[skipStack.length - 1] || (line === 'endif::[]' && line))) {
          if (line === match) return undef(skipStack.pop()) || accum
          if (match === 'endif::[]' && line.startsWith('if') && /^ifn?def::.+\[\]$/.test(line)) skipStack.push(match)
          return accum
        } else if (!line && !inContainer.verbatim) {
          // Add lead class to the end of the paragraph if needed
          if (attrs.has('_lead_paragraph') && accum.length > 0) {
            accum[accum.length - 1] += ' {{ className: \'lead\' }}'
            attrs.delete('_lead_paragraph')
          }
          if (inTable || (inHeader = inPara = false)) return accum
          inList ? (inPara = undefined) : (line = indent = inContainer.childIndent || '') && (line = line.trimEnd())
          blockAttrs = blockTitle = verbatim = verbatim?.close()
          return accum[accum.length - 1] && (accum[accum.length] = line) ? accum : accum
        } else if (!inContainer.isDiagram && ((grab = (chr0 = line[0]) === '\\') || (chr0 === 'i' && line[1] !== 'm')) &&
            ((grab && line === '\\endif::[]') || (line[line.length - 1] === ']' && ~line.indexOf('::') &&
            (match = PreprocessorDirectiveRx.exec(line)))) && !(line = grab ? line.substring(1) : undefined)) {
          if (match[1]) {
            const [,, negated, name, text, drop = attrs.has(name) ? !!negated : !negated] = match
            if (text ? (drop ? false : (line = text)) : !skipStack.push(drop && 'endif::[]')) continue // redo
          } else if (!match[1] && match[3]) {
            const includePath = resolveIncludePath(match[3], basePath)
            if (!includedPaths.has(includePath)) {
              try {
                const includeContent = fs.readFileSync(includePath, 'utf8')
                const processedInclude = downdoc(includeContent, {
                  attributes: Object.fromEntries(attrs),
                  basePath: path.dirname(includePath),
                  includedPaths: new Set([...includedPaths, includePath]),
                })
                const includeLines = processedInclude.split('\n')
                accum.push.apply(accum, includeLines.map((l) => (indent || '') + l))
                return accum
              } catch (err) {
                line = undefined
              }
            } else {
              line = undefined
            }
          }
        } else if (inContainer.verbatim) {
          if (line === inContainer.delimiter) {
            // Handle diagram block closing - convert DOT to SVG
            if (inContainer.isDiagram) {
              const dotSource = inContainer.diagramLines.join('\n')
              const svg = convertDotToSvg(dotSource)
              if (svg) {
                // Successfully converted - output the SVG
                accum.push(inContainer.diagramIndent + svg)
              } else {
                // Fallback to code block if graphviz not available
                accum.push(inContainer.diagramIndent + '```dot')
                for (const diagramLine of inContainer.diagramLines) {
                  accum.push(inContainer.diagramIndent + diagramLine)
                }
                accum.push(inContainer.diagramIndent + '```')
              }
              line = undefined
            } else {
              ;({ cap: line, indent, inList, listStack } = inContainer)
              if (inContainer.outdent && (grab = inContainer.outdent + indent.length) && ~(match = inContainer.at)) {
                for (let i = match, l = accum.length; ++i < l;) accum[i] = (indent + accum[i].substring(grab)).trimEnd()
              }
            }
            inContainer = containerStack.length ? containerStack.pop() : false
          } else if (inContainer.isDiagram) {
            // Collect diagram content lines, resolving includes
            const includeMatch = /^include::([^\[]+)\[\]$/.exec(line)
            if (includeMatch) {
              try {
                const includePath = resolveIncludePath(includeMatch[1], basePath)
                const includeContent = fs.readFileSync(includePath, 'utf8')
                inContainer.diagramLines.push(...includeContent.split('\n'))
              } catch (err) {
                // If include fails, add the line as-is
                inContainer.diagramLines.push(line)
              }
            } else {
              inContainer.diagramLines.push(line)
            }
            line = undefined
          } else if ((match = line.length)) {
            inContainer.outdent &&= Math.min(match - line.trimStart().length, inContainer.outdent)
            if (match > 2 && (~line.indexOf('{') || line[match - 1] === '>')) subs = inContainer.subs
          }
        } else if (!inHeader && delimOf(line)) {
          if (inPara !== false) inPara = !(listStack = (inList = undef((indent = inContainer.childIndent || ''))) || [])
          const opening = inContainer === false || (line !== inContainer.delimiter && containerStack.push(inContainer))
            ? (inContainer = { delimiter: line, indent, childIndent: indent, inList, listStack })
            : undefined
          if ((grab = DELIMS[delimOf(line)]) === 'v') {
            inContainer.subs = (inContainer.verbatim = !!(attrs.coseq = 1)) && ['callouts']
            if (blockAttrs) {
              style = ((style = blockAttrs.get(1) || (delimOf(line) === '----' ? 'source' : undefined)) === 'source')
                ? blockAttrs.get(2) || attrs.get('source-language')
                : style === 'listing' || style === 'literal' ? undefined : style
              if (blockAttrs.get('indent') === '0') Object.assign(inContainer, { at: accum.length, outdent: Infinity })
              if (blockAttrs.get('subs')?.includes('attributes')) inContainer.subs.push('attributes')
              blockTitle &&= writeBlockTitle(accum, blockTitle, blockAttrs, attrs, refs)
            } else if (delimOf(line) === '----') style = attrs.get('source-language')
            // Check if this is a graphviz/dot diagram block
            if (style in DIAGRAM_STYLES) {
              inContainer.isDiagram = true
              inContainer.diagramLines = []
              inContainer.diagramIndent = indent
              line = undefined // Don't output opening delimiter for diagrams
            } else if (containerStack.length && containerStack[containerStack.length - 1].isTabsContainer && containerStack[containerStack.length - 1].currentTabTitle) {
              const tabTitle = containerStack[containerStack.length - 1].currentTabTitle
              const mappedStyle = style && (LANGUAGE_MAP[style] || style)
              line = mappedStyle ? '```' + mappedStyle + ' {{ title: \'' + tabTitle + '\' }}' : '```' + ' {{ title: \'' + tabTitle + '\' }}'
              inContainer.cap = '```'
              // Clear the tab title after use
              containerStack[containerStack.length - 1].currentTabTitle = undefined
            } else {
              const mappedStyle = style && (LANGUAGE_MAP[style] || style)
              line = mappedStyle ? (inContainer.cap = '```') + mappedStyle : (inContainer.cap = '```')
            }
          } else if (grab === 'p' && (inContainer.verbatim = true)) {
            line = blockAttrs && blockAttrs.get(1) === 'stem' ? (inContainer.cap = '```') + 'math' : undefined
            blockTitle = undefined
          } else if (opening === undefined) {
            ;({ cap: line, indent, inList, listStack } = inContainer)
            inTable = blockTitle = undefined
            inContainer = containerStack.length ? containerStack.pop() : false
          } else if (grab === 't') {
            inTable = { header: blockAttrs?.has('header-option') || (!blockAttrs?.has('noheader-option') && undefined) }
            if (blockAttrs !== (line = undefined) && (grab = blockAttrs.get('cols'))) {
              const cols = (!~grab.indexOf('*') && grab.split(/,|;/)) || grab.split(/,|;/)
                .reduce((a, c) => a.push.apply(a, ~c.indexOf('*') ? Array(parseInt(c, 10)).fill(c) : [c]) && a, [])
              ;(inTable.div = ~grab.indexOf('<') || ~grab.indexOf('^') || ~grab.indexOf('>')
                ? cols.reduce((buf, c) => buf + TDIV[/(?<!\.)[<^>]|$/.exec(c)[0]], '') + '|'
                : TDIV[''].repeat(cols.length) + '|') && (inTable.cols = cols.length)
            }
          } else if (delimOf(line) === '____') {
            indent = inContainer.childIndent += '> '
            if ((grab = blockAttrs && blockAttrs.get(2))) inContainer.cap = '>\n' + indent + '\u2014 ' + grab
            line = blockTitle &&= writeBlockTitle(accum, blockTitle, blockAttrs, attrs, refs)
          } else if (delimOf(line) === '====' && blockAttrs) {
            if ((style = blockAttrs.get(1)) in ADMONS) {
              const tagName = style === 'NOTE' ? 'Note' :
                              style === 'IMPORTANT' ? 'Important' :
                              style === 'WARNING' ? 'Warning' :
                              style === 'CAUTION' ? 'Caution' :
                              style === 'TIP' ? 'Tip' : style
              line = '<' + tagName + (blockAttrs.has('id') ? ' id="' + blockAttrs.get('id') + '"' : '') + '>'
              inContainer.cap = '</' + tagName + '>'
              blockTitle = undefined
            } else if (blockAttrs.has('collapsible-option')) {
              line = attrs.get('markdown-collapsible-variant') === 'spoiler' && (grab = 'spoiler')
                ? (inContainer.cap = '```') + (blockTitle ? grab + ' ' + applySubs.call(attrs, blockTitle.text) : grab)
                : (inContainer.cap = '</details>') && (blockAttrs.has('open-option') ? '<details open>' : '<details>') +
                  '\n' + indent + '<summary>' + (blockTitle ? blockTitle.text : 'Details') + '</summary>\n'
              blockTitle = undefined
            } else if (blockAttrs.get(1) === 'tabs') {
              // Handle tabs as CodeGroup for MDX
              inContainer.isTabsContainer = true
              line = '<CodeGroup' + (blockTitle ? ' title="' + blockTitle.text + '"' : '') + '>'
              inContainer.cap = '</CodeGroup>'
              blockTitle = undefined
            } else line = blockTitle &&= writeBlockTitle(accum, blockTitle, blockAttrs, attrs, refs)
          } else line = blockTitle &&= writeBlockTitle(accum, blockTitle, blockAttrs, attrs, refs)
          if (opening !== (blockAttrs = undefined)) listStack = (inList = undefined) || []
        } else if (!inHeader && line.startsWith('```')) {
          // Handle fenced code blocks from Markdown-style input
          if (inPara !== false) inPara = !(listStack = (inList = undef((indent = inContainer.childIndent || ''))) || [])
          const opening = inContainer === false || (line !== inContainer.delimiter && containerStack.push(inContainer))
            ? (inContainer = { delimiter: '```', indent, childIndent: indent, inList, listStack })
            : undefined
          if (opening !== undefined) {
            inContainer.subs = (inContainer.verbatim = !!(attrs.coseq = 1)) && ['callouts']
            style = line.length > 3 ? line.substring(3) : undefined
            inContainer.cap = '```'
            line = style ? '```' + style : '```'
            blockTitle = undefined
          } else {
            // Closing fenced block
            ;({ cap: line, indent, inList, listStack } = inContainer)
            inContainer = containerStack.length ? containerStack.pop() : false
          }
          if (opening !== (blockAttrs = undefined)) listStack = (inList = undefined) || []
        } else {
          let _chr0, _line, indented
          if (!(indented = chr0 === ' ')) _line = line
          if (inPara === undefined && !(inPara = false) && (_chr0 = indented ? (_line = line.trimStart())[0] : chr0)) {
            isAnyListItem(_chr0, _line) && inList
              ? accum.pop()
              : !indented && (listStack = (inList = undef((indent = inContainer.childIndent || ''))) || [])
          }
          if (chr0 === '/' && line[1] === '/') {
            line = line === '////' ? undef((inPara = !(skipStack.push(line)))) : undefined
          } else if (!inPara && chr0 === '=' && (match = isHeading(line, inContainer === false, blockAttrs))) {
            let [marker, title, id, autoId] = match
            if (inHeader) {
              if (marker.length > 1 || (blockAttrs && blockAttrs.get(1) === 'discrete') || attrs.has('doctitle')) {
                if (!(inHeader = false) && accum.length) return accum
                continue // redo
              }
              attrs.set('doctitle', title)
              if ((id = blockAttrs?.get('id'))) autoId = title.toLowerCase().split(' ').join('-')
            } else {
              autoId = (grab = (title = attributes.call(attrs, title)).toLowerCase().split(' ')).join('-')
              id = blockAttrs?.get('id') || attrs.get('idprefix') + grab.join(attrs.get('idseparator'))
            }
            if (id) refs.set(title, refs.set(id, { autoId, reftext: blockAttrs?.get('reftext'), title }).get(id))
            blockAttrs = blockTitle = undefined
            if (marker.length === 1) {
              line = '**' + title + '**'
              // Track if this is a top-level heading (original H1) for lead paragraph styling
              attrs.set('_after_h1', 'true')
            } else {
              line = '#'.repeat(marker.length - 1) + ' ' + title
              // Track if this is a top-level heading (h1) for lead paragraph styling
              if (marker.length === 2) {
                attrs.set('_after_h1', 'true')
              }
            }
          } else if (!inPara && chr0 === ':' && (match = AttributeEntryRx.exec(line))) {
            const [, del, name, val = ''] = (line = undefined) || match
            if (!(name in initialAttrs)) del ? attrs.delete(name) : attrs.set(name, val && attributes.call(attrs, val))
          } else if (chr0 === '[' && line[line.length - 1] === ']') {
            if (verbatim && !(inPara = verbatim = verbatim.close())) continue // redo
            // Check if this is an inline anchor [[id]] rather than block attributes [id]
            if (line.startsWith('[[') && line.endsWith(']]') && InlineAnchorRx.test(line)) {
              // Process as inline anchor and reset paragraph state for next line
              subs = NORMAL_SUBS
              inPara = false
            } else {
              blockAttrs = parseAttrlist(line.substring(1, line.length - 1), blockAttrs)
              line = (inPara = false) || undefined
            }
          } else if (inHeader) {
            if ((inHeader = attrs.has('doctitle'))) {
              if (!attrs.has('author') && AuthorInfoLineRx.test(line)) {
                const authors = line.split('; ').map((it) => it.split(' <')[0])
                attrs.set('author', authors[0]).set('authors', authors.join(', '))
              } else if (!('revdate' in attrs) && !('revnumber' in attrs) && (match = RevisionInfoLineRx.exec(line))) {
                const [, revnumber, revdate_, revdate = revdate_] = match
                ;(revnumber ? attrs.set('revnumber', revnumber) : true) && revdate && attrs.set('revdate', revdate)
              } else inHeader = false
            }
            if (!inHeader && !accum.length) continue // redo
            line = undefined
          } else if (inTable) {
            const row = inTable.row
            const cells = ~line.indexOf('|', 1)
              ? line.split(CellDelimiterRx)
              : chr0 === '|' ? ['', line.substring(line[1] === ' ' ? 2 : 1)] : [line]
            if (row) {
              if (cells[0]) {
                if (row.length && (row.wrapped = true)) {
                  row[row.length - 1] = ((grab = row[row.length - 1]) && hardbreak(grab, ' +\n') + ' ') + cells[0]
                } else {
                  line = (grab = accum[accum.length - 1].split('\n'))[0].substring(0, grab[0].length - 2).trimEnd()
                  line = hardbreak(line, '<br />') + ' ' + applySubs.call(attrs, cells[0]) + ' |'
                  accum[accum.length - 1] = grab.length > 1 ? (grab[0] = line) && grab.join('\n') : line
                }
              }
              if ((cells.length === 1 ? row.length : row.push.apply(row, cells.slice(1))) < inTable.cols) return accum
              line = '| ' + applySubs.call(attrs, row.splice(0, inTable.cols).join(' | ')) + ' |'
              if (row.wrapped && !(row.wrapped = false) && ~line.indexOf(' +\n')) line = line.replace(/ \+\n/g, '<br />')
              if (row.length && accum.push(indent + line) && (line = '|' + row.splice(0).join(' |'))) continue // redo
            } else {
              const cols = (inTable.row = []) && (inTable.cols ??= cells.length - 1)
              if (!(inTable.header ??= cols === cells.length - 1 && lines[idx + 1] === '' && lines[idx - 1] !== '')) {
                blockTitle &&= writeBlockTitle(accum, blockTitle, blockAttrs, attrs, refs)
                accum.push(indent + '|     '.repeat(cols) + '|', indent + (inTable.div || TDIV[''].repeat(cols) + '|'))
                continue // redo
              }
              subs = NORMAL_SUBS
              line = '| ' + cells.slice(1).join(' | ') + ' |\n' + indent + (inTable.div || TDIV[''].repeat(cols) + '|')
            }
          } else if (line === '+' && inList) {
            if (inContainer && inContainer.isTabsContainer) {
              // Skip continuation markers in tabs containers
              return accum
            }
            ;({ indent: line, childIndent: indent } = inList)
            verbatim = (inPara = false) || verbatim?.close()
            return (accum[accum.length] = line && line.trimEnd()) ? accum : accum // eslint-disable-line no-cond-assign
          } else if ((!inPara || inList) && (_chr0 ??= indented ? (_line = line.trimStart())[0] : chr0) &&
              (match = isAnyListItem(_chr0, _line, 'exec'))) {
            let [, marker, text, desc, dlist] = match
            if (dlist !== undefined && (dlist = text)) { // marker and text are swapped for dlist item
              if (inContainer.isTabsContainer) {
                // Handle tab items for CodeGroup - store the tab title for later use
                inContainer.currentTabTitle = marker
                // Set up minimal list context to handle continuation markers
                if (!inList) {
                  indent = inContainer.childIndent || ''
                  inList = { marker: dlist, indent, childIndent: indent }
                }
                line = undefined // Skip the tab title line, we'll handle the content directly
                return accum
              }
              (blockAttrs && blockAttrs.get(1) === 'qanda') || (inList && inList.dlist === 'qanda')
                ? (text = '_' + marker + '_') && (marker = '.'.repeat(dlist.length - 1)) && (dlist = 'qanda')
                : (text = '*' + marker + '*') && (marker = dlist.length > 2 ? '-'.repeat(dlist.length - 1) : '-')
              if (!(next = desc)) hardbreakNext = 'pending'
            }
            const ordered = (marker[0] === '<' && !!(marker = '<.>')) || marker[0] === '.' ||
               (marker[marker.length - 1] === '.' && !!(marker = '1.'))
            if (!inList || inList.marker !== marker) {
              if ((listStack.length && ~(match = listStack.findIndex((it) => it.marker === marker)))) {
                indent = (inList = (listStack = match ? listStack.slice(0, match + 1) : [listStack[0]]).pop()).indent
              } else {
                indent = (inList ? (listStack[listStack.length] = inList) : inContainer).childIndent || ''
                const lindent = (attrs.lindent ??= parseInt(attrs.get('markdown-list-indent'), 10)) || (ordered ? 3 : 2)
                inList = { marker, indent, childIndent: indent + ' '.repeat(lindent), numeral: ordered && 0, dlist }
              }
            } else indent = inList.indent
            verbatim = verbatim?.close()
            subs = (inPara = true) && NORMAL_SUBS
            line = (ordered ? ++inList.numeral + '. ' : '* ') + text
          } else if (inPara) {
            subs = NORMAL_SUBS
            if (verbatim) {
              if (indented ? undef((subs = verbatim.subs)) : !(inPara = verbatim = verbatim.close())) continue // redo
              line = line.substring(verbatim.outdent)
            } else if (hardbreakNext || inPara === 'hardbreaks') {
              accum[accum.length - 1] += attrs.get('markdown-line-break')
            } else if ((grab = accum[accum.length - 1])?.[grab.length - 1] === '+' && grab[grab.length - 2] === ' ') {
              accum[accum.length - 1] = hardbreak(grab, attrs.get('markdown-line-break'), true)
            } else if (attrs.has('markdown-unwrap-prose')) {
              ;(inPara !== '> ' || ((line = line.trimEnd()) !== '>' && accum[accum.length - 1] !== '>' &&
                (line = line.substring(2)))) && (indent = accum.pop() + ' ')
            }
          } else if (chr0 === '.') {
            subs = NORMAL_SUBS
            if (line !== chr0 && !(line[1] === '.' && line[2] === '.') && (match = line.length - 1)) {
              const text = line[1] === '*' && line[match] === '*' ? line.substring(2, match) : line.substring(1)
              blockTitle = (line = undefined) || { indent, text, subs }
            }
          } else if (indented && !inContainer.verbatim) {
            if (blockAttrs && blockAttrs.get('subs')?.includes('attributes')) subs = ['attributes']
            const outdent = line.length - (line = _line).length
            if ((inPara = true) && _chr0 === '$' && _line[1] === ' ') {
              indent = (inList || inContainer).childIndent || ''
              verbatim = { cap: indent + '```', close: () => accum.push(verbatim.cap) && undefined, outdent, subs }
              line = '```console\n' + indent + line
            } else {
              indent = (inList || inContainer).childIndent || ''
              verbatim = { cap: indent + '```', close: () => accum.push(verbatim.cap) && undefined, outdent, subs }
              line = '```\n' + indent + line
            }
          } else if (~(match = line.indexOf(': ')) && match < 10 && (style = line.substring(0, match)) in ADMONS) {
            next = (inPara = true) && line.substring(match + 2)
            const tagName = style === 'NOTE' ? 'Note' :
                            style === 'IMPORTANT' ? 'Important' :
                            style === 'WARNING' ? 'Warning' :
                            style === 'CAUTION' ? 'Caution' :
                            style === 'TIP' ? 'Tip' : style
            line = '<' + tagName + '>'
            // Set up a custom closing that will be handled after the next content
            attrs.set('_admonition_closing', '</' + tagName + '>')
          } else if (chr0 === 'i' && line.startsWith('image::') && (match = BlockImageMacroRx.exec(line))) {
            line = image.apply(attrs, match, (subs = ['attributes']))
          } else if (line in BREAKS) {
            line = BREAKS[line]
          } else {
            inPara = blockAttrs?.has('hardbreaks-option') ? 'hardbreaks' : chr0 === '>' && line[1] === ' ' ? '> ' : true
            if ((grab = blockAttrs?.get('id'))) blockTitle ? (blockTitle.id = grab) : (line = '[[' + grab + ']]' + line)

            // Mark this paragraph as needing lead class (will be added at the end)
            if (attrs.has('_after_h1')) {
              attrs.set('_lead_paragraph', 'true')
              attrs.delete('_after_h1')
            }

            subs = NORMAL_SUBS
          }
        }
        if (line) {
          blockTitle &&= writeBlockTitle(accum, blockTitle, blockAttrs, attrs, refs)
          if (subs && !(line = applySubs.call(attrs, line, subs)) && !accum.length) return accum
          accum[accum.length] = indent && line ? indent + line : line
          if (next && (next = applySubs.call(attrs, next))) {
            if (attrs.has('_admonition_closing')) {
              // Format admonition with proper indentation
              accum[accum.length] = '  ' + next
              accum[accum.length] = attrs.get('_admonition_closing')
              attrs.delete('_admonition_closing')
            } else {
              accum[accum.length - 1] += attrs.get('markdown-line-break')
              accum[accum.length] = indent ? indent + next : next
            }
          }
        } else if (line === undefined) {
          return accum
        } else accum[accum.length] = indent ? indent.trimEnd() : line
        hardbreakNext &&= hardbreakNext === 'pending' || undefined
        return accum
      }
    }, [])
    .map((line, idx, arr) => {
      // Handle lead class for last paragraph if document ends without empty line
      if (idx === arr.length - 1 && attrs.has('_lead_paragraph')) {
        attrs.delete('_lead_paragraph')
        return line + ' {{ className: \'lead\' }}'
      }
      return line
    })
    .join('\n')
    .trimEnd()
    .replace(RewriteInternalXrefRx, (_, text, id) => {
      // Handle cross-page links that start with /
      if (id.startsWith('/')) {
        return '[' + text + '](' + id + ')'
      }
      const { title = id, reftext = title, autoId = id } = refs.get(id) || nrefs.get(id) || {}
      return '[' + (text || reftext) + '](#' + autoId + ')'
    })
    .concat(((grab = verbatim?.cap)) ? '\n' + grab : '') // prettier-ignore
}

function applySubs (str, subs = NORMAL_SUBS) {
  if (!/[{\x60\x27*_:<[#]/.test(str)) return str
  str = subs.reduce((str, name) => SUBSTITUTORS[name].call(this, str), str)
  // Escape remaining curly braces for MDX (but not {{ which is intentional MDX syntax)
  if (~str.indexOf('{')) str = str.replace(/(?<!\{)\{(?!\{)(\w)/g, '\\{$1')
  return str
}

function attributes (str) {
  return ~str.indexOf('{') ? str.replace(AttributeRefRx, (m, bs, n) => (bs ? m.substring(1) : this.get(n) ?? m)) : str
}

function callouts (str, apply = str[str.length - 1] === '>') {
  return apply ? str.replace(ConumRx, (_, sp, chr) => sp + CONUMS[chr === '.' ? this.coseq++ : chr]) : str
}

function hardbreak (str, mark, force, len = str.length) {
  return force || (str[len - 1] === '+' && str[len - 2] === ' ') ? str.substring(0, str.length - 2) + mark : str
}

function image (_, target, attrlist, _idx, _str, alt = attrlist.split(',')[0] || /(.*\/)?(.*?)($|\.)/.exec(target)[2]) {
  return '![' + alt + '](' + (this.get('imagesdir') ? this.get('imagesdir') + '/' : '') + target + ')'
}

function delimOf (line) {
  if (line in DELIMS) return line
  if (line.length > 4 && DELIM_CHARS.has(line[0]) && line[0].repeat(line.length) === line) return line[0].repeat(4)
}

function isAnyListItem (chr0, str, mode = 'test', match = chr0 in LIST_MARKERS && ListItemRx[mode](str)) {
  return match || (str.endsWith('::') || ~str.indexOf(':: ') ? DlistItemRx[mode](str) : undefined)
}

function isHeading (str, acceptAll, blockAttrs, marker, title, spaceIdx = str.indexOf(' ')) {
  if (!(~spaceIdx && str.startsWith((marker = ['=', '==', '===', '====', '=====', '======'][spaceIdx - 1])))) return
  if (!(title = str.substring(spaceIdx + 1)) || (title[0] === ' ' && !(title = title.trimStart()))) return
  if (acceptAll || (blockAttrs && blockAttrs.get(1) === 'discrete')) return [marker, title]
}

function macros (str) {
  if (!~str.indexOf(':')) return ~str.indexOf('[[') ? str.replace(InlineAnchorRx, (_, id) => {
    // Only create anchor if it has __ (fragment). Otherwise skip - it's a normal URL
    const fragmentIndex = id.indexOf('__')
    if (fragmentIndex >= 0) {
      const anchorId = id.substring(fragmentIndex + 2)
      return '<a id="' + anchorId + '"/>'
    }
    return '' // Skip anchors without __ completely
  }) : str
  if (~str.indexOf('m:[')) str = str.replace(InlineStemMacroRx, (_, expr) => '$' + expr.replace(/\\]/g, ']') + '$')
  if (~str.indexOf('image:')) str = str.replace(InlineImageMacroRx, image.bind(this))
  if (~str.indexOf(':/') || ~str.indexOf('link:')) {
    str = str.replace(LinkMacroRx, (_, esc, scheme = '', url, boxed = '', text, bareScheme = scheme, bareUrl) => {
      if (esc) return bareScheme ? '<span>' + bareScheme + '</span>' + (bareUrl ?? url + boxed) : 'link:' + url + boxed
      if (!bareUrl) return '[' + (text ||= this.has('hide-uri-scheme') ? url : scheme + url) + '](' + scheme + url + ')'
      return this.has('hide-uri-scheme') ? '[' + bareUrl + '](' + bareScheme + bareUrl + ')' : bareScheme + bareUrl
    })
  }
  if (~str.indexOf('[[')) str = str.replace(InlineAnchorRx, (_, id) => {
    // Only create anchor if it has __ (fragment). Otherwise skip - it's a normal URL
    const fragmentIndex = id.indexOf('__')
    if (fragmentIndex >= 0) {
      const anchorId = id.substring(fragmentIndex + 2)
      return '<a id="' + anchorId + '"/>'
    }
    return '' // Skip anchors without __ completely
  })
  if (!~str.indexOf('xref:')) return str
  return str.replace(XrefMacroRx, (m, esc, p, ext, id_, id = id_, txt) =>
    esc ? m.substring(1) : '[' + (p && (ext === '#' || (p += ext)) ? txt || p : (p = '#!' + id) && txt) + '](' + p + ')'
  )
}

function parseAttrlist (attrlist, attrs = new Map()) {
  if (!attrlist) return attrs
  attrs.set(0, attrlist)
  let chr0, idx, m, shorthand, style
  if ((chr0 = attrlist[0]) === '[' && (m = BlockAnchorRx.exec(attrlist))) {
    return m[2] ? attrs.set('id', m[1]).set('reftext', m[2]) : attrs.set('id', m[1])
  }
  if (!(idx = 0) && (~attrlist.indexOf('=') || ~attrlist.indexOf('"'))) {
    while ((m = ElementAttributeRx.exec(attrlist))) {
      attrs.set(m[1] ?? ++idx, m[4] ?? m[3])
      if (!m.index) attrlist = (ElementAttributeRx.lastIndex = 1) && ',' + attrlist
    }
  } else if (chr0 === ',' || ~attrlist.indexOf(',')) {
    for (const it of attrlist.split(',')) attrs.set(++idx, it.trimStart())
  } else attrs.set(1, attrlist)
  if (!(shorthand = attrs.get(1)) || (m = shorthand.split(StyleShorthandMarkersRx)).length < 2) return attrs
  for (let i = 0, len = m.length, val; i < len; i += 2) {
    if ((val = m[i]) && ((chr0 = m[i - 1]) || !(style = val))) {
      chr0 === '#' ? attrs.set('id', val) : chr0 === '.' ? attrs.set('role', val) : attrs.set(val + '-option', '')
    }
  }
  return attrs.set(1, style)
}

function quotes (str, idx) {
  const hasLt = ~(~str.indexOf('<<') ? (str = str.replace(XrefShorthandRx, (_, target, text) => {
    // ALWAYS convert to URL starting with /: reference.tools -> /reference/tools
    // Convert . to / and __ to #
    const url = '/' + target.replace(/\./g, '/').replace(/__/g, '#')
    return 'xref:' + url + '[' + (text || '') + ']'
  })) : str).indexOf('<')
  if (hasLt) str = str.replace(/</g, '&lt;')
  if (~(idx = str.indexOf('*')) && ~str.indexOf('*', idx + 1)) str = str.replace(StrongSpanRx, '*$1*')
  if (~str.indexOf('`') && ((idx = ~str.indexOf('"`') || ~str.indexOf("'`")) || true)) {
    if (idx) str = str.replace(QuotedSpanRx, (this.q ??= this.get('quotes').split(' ').slice(0, 2).join('$2')))
    if (hasLt || ~str.indexOf('`+') || ~str.indexOf(']`') || ~str.indexOf('\\')) {
      str = str.replace(/(?:\[[^[\]]+\])?`(\+)?(\S|\S.*?\S)\1`/g, (_, pass, text) => {
        if (hasLt && text.length > 3 && ~text.indexOf('&lt;')) text = text.replace(/&lt;/g, '<')
        if (pass) return '`' + (~text.indexOf('{') ? text.replace(/\{(?=[a-z])/g, '\\{') : text) + '`'
        return '`' + (~text.indexOf('\\') ? text.replace(/\\(?=https?:|\.\.\.)/g, '') : text) + '`'
      })
    }
  }
  if (~str.indexOf(']_')) str = str.replace(EmphasisSpanMetaRx, '')
  if (~(idx = str.indexOf('#')) && ~str.indexOf('#', idx + 1)) {
    str = str.replace(MarkedSpanRx, (_, roles, s, text) => {
      s &&= this.s ??= (s = this.get('markdown-strikethrough').split(' ')).length > 1 ? s.slice(0, 2) : [s[0], s[0]]
      return roles ? (s ? s[0] + text + s[1] : text) : '<mark>' + text + '</mark>'
    })
  }
  if (!~str.indexOf("'")) return str
  return str.replace(/.'/g, (m, i, s, l = m[0], r = s[i + 2] || '') =>
    l === '`' ? (r === '`' ? m : '\u2019') : /\p{L}/u.test(r) && /[\p{L}\d]/u.test(l) ? l + '\u2019' : m
  )
}

function resolveIncludePath (includePath, basePath) {
  return path.isAbsolute(includePath) ? includePath : path.resolve(basePath, includePath)
}

// Color mapping from graphviz colors to CSS variables with light mode defaults
const DIAGRAM_COLORS = {
  // Fill colors - map to semantic CSS variables
  lightblue: 'var(--diagram-primary,#d1fae5)',
  lightseagreen: 'var(--diagram-primary,#d1fae5)',
  lightgreen: 'var(--diagram-secondary,#e0f2fe)',
  lightyellow: 'var(--diagram-tertiary,#fef3c7)',
  lightsalmon: 'var(--diagram-tertiary,#fef3c7)',
  lightcoral: 'var(--diagram-warning,#ffe4e6)',
  pink: 'var(--diagram-warning,#ffe4e6)',
  lightpink: 'var(--diagram-warning,#ffe4e6)',
  lightgrey: 'var(--diagram-neutral,#f4f4f5)',
  lightsteelblue: 'var(--diagram-neutral,#f4f4f5)',
  lavender: 'var(--diagram-annotation,#f3e8ff)',
  lightcyan: 'var(--diagram-annotation,#f3e8ff)',
  white: 'var(--diagram-bg,#ffffff)',
}

function convertDotToSvg (dotSource) {
  try {
    let svg = execSync('dot -Tsvg', { input: dotSource, encoding: 'utf8', stdio: ['pipe', 'pipe', 'pipe'] })
    // Remove XML declaration, DOCTYPE, and HTML comments (not valid in MDX)
    // Convert SVG attributes to React/JSX compatible camelCase
    svg = svg
      .replace(/^<\?xml[^?]*\?>\s*/i, '')
      .replace(/<!DOCTYPE[^>]*>\s*/i, '')
      .replace(/<!--[\s\S]*?-->\s*/g, '')
      // Remove fixed dimensions, let viewBox control sizing
      .replace(/<svg([^>]*) width="[^"]*"/g, '<svg$1')
      .replace(/<svg([^>]*) height="[^"]*"/g, '<svg$1')
      // Remove background polygon for transparency
      .replace(/<polygon fill="white" stroke="(?:none|transparent)" points="[^"]*"\/>/g, '')

    // Map graphviz colors to CSS variables
    for (const [color, cssVar] of Object.entries(DIAGRAM_COLORS)) {
      svg = svg.replace(new RegExp('fill="' + color + '"', 'g'), 'fill="' + cssVar + '"')
    }

    // Map stroke and text colors
    svg = svg
      // Edge strokes (lines between nodes)
      .replace(/stroke="black"/g, 'stroke="var(--diagram-edge,#71717a)"')
      // Text color
      .replace(/<text([^>]*)>/g, (match, attrs) => {
        if (!attrs.includes('fill=')) {
          return '<text' + attrs + ' fill="var(--diagram-text,#18181b)">'
        }
        return match
      })
      // Arrow polygons (edge arrows)
      .replace(/<polygon fill="black" stroke="black"/g, '<polygon fill="var(--diagram-edge,#71717a)" stroke="var(--diagram-edge,#71717a)"')

    // Continue with JSX attribute conversions
    svg = svg
      // XML namespace attributes
      .replace(/xml:space=/g, 'xmlSpace=')
      .replace(/xlink:href=/g, 'xlinkHref=')
      .replace(/xlink:title=/g, 'xlinkTitle=')
      .replace(/xmlns:xlink=/g, 'xmlnsXlink=')
      // React DOM attribute conversions
      .replace(/ class="/g, ' className="')
      // Hyphenated SVG attributes to camelCase
      .replace(/text-anchor=/g, 'textAnchor=')
      .replace(/font-family=/g, 'fontFamily=')
      .replace(/font-size=/g, 'fontSize=')
      .replace(/font-weight=/g, 'fontWeight=')
      .replace(/font-style=/g, 'fontStyle=')
      .replace(/stroke-width=/g, 'strokeWidth=')
      .replace(/stroke-dasharray=/g, 'strokeDasharray=')
      .replace(/stroke-linecap=/g, 'strokeLinecap=')
      .replace(/stroke-linejoin=/g, 'strokeLinejoin=')
      .replace(/stroke-opacity=/g, 'strokeOpacity=')
      .replace(/fill-opacity=/g, 'fillOpacity=')
      .replace(/fill-rule=/g, 'fillRule=')
      .replace(/clip-path=/g, 'clipPath=')
      .replace(/clip-rule=/g, 'clipRule=')
      .replace(/dominant-baseline=/g, 'dominantBaseline=')
      .replace(/alignment-baseline=/g, 'alignmentBaseline=')
      .replace(/baseline-shift=/g, 'baselineShift=')
      .replace(/stop-color=/g, 'stopColor=')
      .replace(/stop-opacity=/g, 'stopOpacity=')
      .trim()

    return svg
  } catch (err) {
    // If graphviz is not installed or fails, return null to fall back to code block
    return null
  }
}

function writeBlockTitle (buffer, blockTitle, blockAttrs, attrs, refs) {
  const { id = blockAttrs?.get('id'), indent, text, subs, title = applySubs.call(attrs, text, subs) } = blockTitle
  const anchor = id && refs.set(id, { title, reftext: blockAttrs.get('reftext') }) ? '<a name="' + id + '"></a>' : ''
  buffer.push(indent + anchor + '**' + title + '**', '')
}
