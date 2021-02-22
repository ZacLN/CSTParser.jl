function longest_common_prefix(prefixa, prefixb)
    maxplength = min(sizeof(prefixa), sizeof(prefixb))
    maxplength == 0 && return ""
    idx = findfirst(i -> (prefixa[i] != prefixb[i]), 1:maxplength)
    idx = idx === nothing ? maxplength : idx - 1
    prefixa[1:idx]
end

function skip_to_nl(str, idxend)
    while (idxend < sizeof(str)) && str[idxend] != '\n'
        idxend = nextind(str, idxend)
    end
    idxend > sizeof(str) ? prevind(str, idxend) : idxend
end

tostr(buf::IOBuffer) = _unescape_string(String(take!(buf)))

"""
parse_string_or_cmd(ps)

When trying to make an `INSTANCE` from a string token we must check for
interpolating opoerators.
"""
function parse_string_or_cmd(ps::ParseState, prefixed=false)
    sfullspan = ps.nt.startbyte - ps.t.startbyte
    sspan = 1 + ps.t.endbyte - ps.t.startbyte

    istrip = (kindof(ps.t) === Tokens.TRIPLE_STRING) || (kindof(ps.t) === Tokens.TRIPLE_CMD)
    iscmd = kindof(ps.t) === Tokens.CMD || kindof(ps.t) === Tokens.TRIPLE_CMD

    lcp = nothing
    exprs_to_adjust = []
    function adjust_lcp(expr::EXPR, last=false)
        if isliteral(expr)
            push!(exprs_to_adjust, expr)
            str = valof(expr)
            (isempty(str) || (lcp !== nothing && isempty(lcp))) && return
            (last && str[end] == '\n') && return (lcp = "")
            idxstart, idxend = 2, 1
            prevpos = idxend
            while nextind(str, idxend) - 1 < sizeof(str) && (lcp === nothing || !isempty(lcp))
                idxend = skip_to_nl(str, idxend)
                idxstart = nextind(str, idxend)
                prevpos1 = idxend
                while nextind(str, idxend) - 1 < sizeof(str)
                    c = str[nextind(str, idxend)]
                    if c == ' ' || c == '\t'
                        idxend += 1
                    elseif c == '\n'
                        # All whitespace lines in the middle are ignored
                        idxend += 1
                        idxstart = idxend + 1
                    else
                        prefix = str[idxstart:idxend]
                        lcp = lcp === nothing ? prefix : longest_common_prefix(lcp, prefix)
                        break
                    end
                    if idxend <= prevpos1
                        throw(CSTInfiniteLoop("Infinite loop in adjust_lcp"))
                    else
                        prevpos1 = idxend
                    end
                end
                if idxend < prevpos
                    throw(CSTInfiniteLoop("Infinite loop in adjust_lcp"))
                else
                    prevpos = idxend
                end
            end
            if idxstart != nextind(str, idxend)
                prefix = str[idxstart:idxend]
                lcp = lcp === nothing ? prefix : longest_common_prefix(lcp, prefix)
            end
        end
    end

    isinterpolated = false
    erroredonlast = false

    t_str = val(ps.t, ps)
    if istrip && length(t_str) == 6
        if iscmd
            return wrapwithcmdmacro(EXPR(:TRIPLESTRING, sfullspan, sspan, ""))
        else
            return EXPR(:TRIPLESTRING, sfullspan, sspan, "")
        end
    elseif length(t_str) == 2
        if iscmd
            return wrapwithcmdmacro(EXPR(:STRING, sfullspan, sspan, ""))
        else
            return EXPR(:STRING, sfullspan, sspan, "")
        end
    elseif prefixed != false || iscmd
        _val = istrip ? t_str[4:prevind(t_str, sizeof(t_str), 3)] : t_str[2:prevind(t_str, sizeof(t_str))]
        if iscmd
            _val = replace(_val, "\\\\" => "\\")
            _val = replace(_val, "\\`" => "`")
        else
            _val = unescape_prefixed(_val)
        end
        expr = EXPR(istrip ? :TRIPLESTRING : :STRING, sfullspan, sspan, _val)
        if istrip
            adjust_lcp(expr)
            ret = EXPR(:string, EXPR[expr], nothing, sfullspan, sspan)
        else
            return iscmd ? wrapwithcmdmacro(expr) : expr
        end
    else
        ret = EXPR(:string, EXPR[], EXPR[], sfullspan, sspan)
        input = IOBuffer(t_str)
        startbytes = istrip ? 3 : 1
        seek(input, startbytes)
        b = IOBuffer()
        safetytrip = 0
        prevpos = position(input)
        while !eof(input)
            c = read(input, Char)
            if c == '\\'
                write(b, c)
                write(b, read(input, Char))
            elseif c == '$'
                isinterpolated = true
                lspan = position(b)
                str = tostr(b)
                ex = EXPR(:STRING, lspan + startbytes, lspan + startbytes, str)
                if position(input) == (istrip ? 3 : 1) + 1
                    # Need to add empty :STRING at start to account for \"
                    pushtotrivia!(ret, ex)
                elseif !isempty(str)
                    push!(ret, ex)
                end
                istrip && adjust_lcp(ex)
                startbytes = 0
                op = EXPR(:OPERATOR, 1, 1, "\$")
                if peekchar(input) == '('
                    skip(input, 1) # skip past '('
                    lpfullspan = -position(input)
                    if iswhitespace(peekchar(input)) || peekchar(input) === '#'
                        read_ws_comment(input, readchar(input))
                    end
                    lparen = EXPR(:LPAREN, lpfullspan + position(input) + 1, 1)
                    rparen = EXPR(:RPAREN, 1, 1)

                    prev_input_size = input.size
                    input.size = input.size - (istrip ? 3 : 1)
                    # We're reusing a portion of the string from `ps` so we need to make sure `ps1` knows where the end of the string is.
                    ps1 = ParseState(input)

                    if kindof(ps1.nt) === Tokens.RPAREN
                        push!(ret, EXPR(:ERRORTOKEN, EXPR[], nothing))
                        pushtotrivia!(ret, op)
                        pushtotrivia!(ret, lparen)
                        pushtotrivia!(ret, rparen)
                        seek(input, ps1.nt.startbyte + 1)
                    else
                        interp_val = @closer ps1 :paren parse_expression(ps1, true)
                        push!(ret, interp_val)
                        pushtotrivia!(ret, op)
                        pushtotrivia!(ret, lparen)
                        if kindof(ps1.nt) === Tokens.RPAREN
                            # Need to check the parenthese were actually closed.
                            pushtotrivia!(ret, rparen)
                            seek(input, ps1.nt.startbyte + 1)
                        else
                            pushtotrivia!(ret, EXPR(:RPAREN, 0, 0))
                            seek(input, ps1.nt.startbyte) # We don't skip ahead one as there wasn't a closing paren
                        end
                    end
                    # Compared to flisp/JuliaParser, we have an extra lookahead token,
                    # so we need to back up one here
                    input.size = prev_input_size
                elseif Tokenize.Lexers.iswhitespace(peekchar(input)) || peekchar(input) === '#'
                    pushtotrivia!(ret, op)
                    push!(ret, mErrorToken(ps, StringInterpolationWithTrailingWhitespace))
                elseif sspan == position(input) + (istrip ? 3 : 1)
                    # Error. We've hit the end of the string
                    pushtotrivia!(ret, op)
                    push!(ret, mErrorToken(ps, StringInterpolationWithTrailingWhitespace))
                else
                    pos = position(input)
                    ps1 = ParseState(input)
                    next(ps1)
                    if kindof(ps1.t) === Tokens.WHITESPACE
                        error("Unexpected whitespace after \$ in String")
                    else
                        t = INSTANCE(ps1)
                    end
                    # Attribute trailing whitespace to the string
                    t = adjustspan(t)
                    push!(ret, t)
                    pushtotrivia!(ret, op)
                    seek(input, pos + t.fullspan)
                end
            else
                write(b, c)
            end
            prevpos = loop_check(input, prevpos)
        end

        # handle last String section
        lspan = position(b)
        if erroredonlast
            ex = EXPR(istrip ? :TRIPLESTRING : :STRING, (istrip ? 3 : 1) + (ps.nt.startbyte - ps.t.endbyte - 1), istrip ? 3 : 1, "")
            pushtotrivia!(ret, ex)
        elseif b.size == 0
            ex = mErrorToken(ps, Unknown)
            push!(ret, ex)
        else
            str = tostr(b)
            if istrip
                str = str[1:prevind(str, lastindex(str), 3)]
                # only mark non-interpolated triple strings
                ex = EXPR(length(ret) == 0 ? :TRIPLESTRING : :STRING, lspan + ps.nt.startbyte - ps.t.endbyte - 1 + startbytes, lspan + startbytes, str)
                adjust_lcp(ex, true)
            else
                str = str[1:prevind(str, lastindex(str))]
                ex = EXPR(:STRING, lspan + ps.nt.startbyte - ps.t.endbyte - 1 + startbytes, lspan + startbytes, str)
            end
            if isempty(str)
                pushtotrivia!(ret, ex)
            else
                push!(ret, ex)
            end
        end
    end
    
    single_string_T = (:STRING, :TRIPLESTRING, literalmap(kindof(ps.t)))
    if istrip
        if lcp !== nothing && !isempty(lcp)
            for expr in exprs_to_adjust
                for (i, a) in enumerate(ret.args)
                    if expr == a
                        ret.args[i].val = replace(valof(expr), "\n$lcp"  => "\n")
                        break
                    end
                end
            end
        end
        # Drop leading newline
        if !isempty(ret.args) && isliteral(ret.args[1]) && headof(ret.args[1]) in single_string_T &&
                !isempty(valof(ret.args[1])) && valof(ret.args[1])[1] == '\n'
            ret.args[1] = dropleadlingnewline(ret.args[1])
        end
    end

    if (length(ret.args) == 1 && isliteral(ret.args[1]) && headof(ret.args[1]) in single_string_T) && !isinterpolated
        ret = ret.args[1]
    end
    update_span!(ret)
    
    return iscmd ? wrapwithcmdmacro(ret) : ret
end

function adjustspan(x::EXPR)
    x.fullspan = x.span
    return x
end

dropleadlingnewline(x::EXPR) = EXPR(headof(x), x.fullspan, x.span, valof(x)[2:end])

wrapwithcmdmacro(x) = EXPR(:macrocall, EXPR[EXPR(:globalrefcmd, 0, 0), EXPR(:NOTHING, 0, 0), x])

"""
    parse_prefixed_string_cmd(ps::ParseState, ret::EXPR)

Parse prefixed strings and commands such as `pre"text"`.
"""
function parse_prefixed_string_cmd(ps::ParseState, ret::EXPR)
    arg = parse_string_or_cmd(next(ps), ret)

    if ret.head === :IDENTIFIER && valof(ret) == "var" && isstringliteral(arg) && VERSION > v"1.3.0-"
        return EXPR(:NONSTDIDENTIFIER, EXPR[ret, arg], nothing)
    elseif headof(arg) === :macrocall && headof(arg.args[1]) === :globalrefcmd
        mname = EXPR(:IDENTIFIER, ret.fullspan, ret.span, string("@", valof(ret), "_cmd")) # NOTE: sizeof(valof(mname)) != mname.span
        return EXPR(:macrocall, EXPR[mname, EXPR(:NOTHING, 0, 0), arg.args[3]], nothing)
    elseif is_getfield(ret)
        if headof(ret.args[2]) === :quote || headof(ret.args[2]) === :quotenode
            str_type = valof(ret.args[2].args[1]) isa String ? valof(ret.args[2].args[1]) : "" # to handle some malformed case
            ret.args[2].args[1] = setparent!(EXPR(:IDENTIFIER, ret.args[2].args[1].fullspan, ret.args[2].args[1].span, string("@", str_type, "_str")), ret.args[2])
        else
            str_type = valof(ret.args[2]) isa String ? valof(ret.args[2]) : "" # to handle some malformed case
            ret.args[2] = EXPR(:IDENTIFIER, ret.args[2].fullspan, ret.args[2].span, string("@", str_type, "_str"))
        end

        return EXPR(:macrocall, EXPR[ret, EXPR(:NOTHING, 0, 0), arg], nothing)
    else
        return EXPR(:macrocall, EXPR[EXPR(:IDENTIFIER, ret.fullspan, ret.span, string("@", valof(ret), "_str")), EXPR(:NOTHING, 0, 0), arg], nothing)
    end
end

function unescape_prefixed(str)
    edits = UnitRange{Int}[]
    start = -1
    for (i, c) in enumerate(str)
        if start == -1 && c === '\\'
            start = i
        end
        if start > -1
            if c === '\\'
            elseif c === '\"'
                push!(edits, start:i)
                start = -1
            else 
                start = -1
            end
        end
    end
    
    if !isempty(edits) || start > -1
        str1 = deepcopy(str)
        if start > -1
            # slashes preceding closing '"'
            n = div(length(start:length(str)), 2) - 1
        str1 = string(str1[1:prevind(str1, start)], repeat("\\", n + 1))
        end

        for e in reverse(edits)
            n = div(length(e), 2) - 1
            str1 = string(str1[1:prevind(str1, first(e))], string(repeat("\\", n), "\""), str1[nextind(str1, last(e)):lastindex(str1)])
            
        end
        return str1
    end
    return str
end
